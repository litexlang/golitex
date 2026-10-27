import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_diagonal_x5f_formula_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_12 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)), (by
  let _object_h13 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)))
  have h_13 : Litex.In _value_i2 _object_h13 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4) _object_h13 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)) h_12)
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.matrixDiagonal _value_i2 _value_i1 h_4 (by
      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)
      exact h_12))
    let _equal_wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i3 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
      have _litex_checked_return : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))) → M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → M.mem ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i3 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3))) _raw_i3 _raw_i4) (Litex.denote (Litex.C (M := M))) := (by
        intro _raw_i3 _raw_i4 h_376 h_381 _
        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_376)
        have h_376 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) := h_376
        have h_377 : Litex.In _value_i3 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i3 h_376).1
              )
          )
        have h_378 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i3 h_376).2.1
              )
          )
        have h_379 : Litex.Le _value_i3 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i3 h_376).2.2
              )
          )
        have h_380 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_376)
              )
          )
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_381)
        have h_381 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) := h_381
        have h_382 : Litex.In _value_i4 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i4 h_381).1
              )
          )
        have h_383 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i4 h_381).2.1
              )
          )
        have h_384 : Litex.Le _value_i4 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i4 h_381).2.2
              )
          )
        have h_385 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_381)
              )
          )
        change (by
          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_3_1 := (let _setElement_0 := _value_i4;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.intersect _wd_3_0 _wd_3_1));
          (Litex.finiteSetSize _wd_2_0 (by
            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_3_1 := (let _setElement_0 := _value_i4;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.intersect _wd_3_0 _wd_3_1))
            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
              let _atomic_wd_3_0 := (let _setElement_0 := _value_i3;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (let _finite_tail_0 := _atomic_wd_3_0;
              let _finite_tail_1 := _finite_tail_0.val.tail;
              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
              _finite_0)) (by
              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (let _finite_tail_0 := _atomic_wd_3_0;
              let _finite_tail_1 := _finite_tail_0.val.tail;
              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
              _finite_0))))));
          let _wd_1_1 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_13 (by
            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))
            exact h_376) True.intro);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_3_1 := (let _setElement_0 := _value_i4;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.intersect _wd_3_0 _wd_3_1));
            (Litex.finiteSetSize _wd_2_0 (by
              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              let _wd_3_1 := (let _setElement_0 := _value_i4;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              (Litex.intersect _wd_3_0 _wd_3_1))
              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                let _atomic_wd_4_0 := (let _setElement_0 := _value_i3;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (let _finite_tail_0 := _atomic_wd_4_0;
                let _finite_tail_1 := _finite_tail_0.val.tail;
                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                _finite_0)) (by
                let _atomic_wd_4_0 := (let _setElement_0 := _value_i4;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (let _finite_tail_0 := _atomic_wd_4_0;
                let _finite_tail_1 := _finite_tail_0.val.tail;
                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                _finite_0))))))
            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
            let _atomic_wd_2_0 := _wd_1_1
            exact (by
              let _litex_return_call := _atomic_wd_2_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
        exact (by
          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_3_1 := (let _setElement_0 := _value_i4;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.intersect _wd_3_0 _wd_3_1));
          (Litex.finiteSetSize _wd_2_0 (by
            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_3_1 := (let _setElement_0 := _value_i4;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.intersect _wd_3_0 _wd_3_1))
            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
              let _atomic_wd_3_0 := (let _setElement_0 := _value_i3;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (let _finite_tail_0 := _atomic_wd_3_0;
              let _finite_tail_1 := _finite_tail_0.val.tail;
              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
              _finite_0)) (by
              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (let _finite_tail_0 := _atomic_wd_3_0;
              let _finite_tail_1 := _finite_tail_0.val.tail;
              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
              _finite_0))))));
          let _wd_1_1 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_13 (by
            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))
            exact h_376) True.intro);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_3_1 := (let _setElement_0 := _value_i4;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.intersect _wd_3_0 _wd_3_1));
            (Litex.finiteSetSize _wd_2_0 (by
              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              let _wd_3_1 := (let _setElement_0 := _value_i4;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              (Litex.intersect _wd_3_0 _wd_3_1))
              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                let _atomic_wd_4_0 := (let _setElement_0 := _value_i3;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (let _finite_tail_0 := _atomic_wd_4_0;
                let _finite_tail_1 := _finite_tail_0.val.tail;
                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                _finite_0)) (by
                let _atomic_wd_4_0 := (let _setElement_0 := _value_i4;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (let _finite_tail_0 := _atomic_wd_4_0;
                let _finite_tail_1 := _finite_tail_0.val.tail;
                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                _finite_0))))))
            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
            let _atomic_wd_2_0 := _wd_1_1
            exact (by
              let _litex_return_call := _atomic_wd_2_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          exact (by
            let _arithmetic := _atomic_wd_1_0
            exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
      intro _litex_input _litex_domain
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_12
          have h_5 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_4)
                )
            )
          let _object_h13 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)))
          have h_13 : Litex.In _value_i2 _object_h13 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4) _object_h13 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)) h_12)
                )
            )
          have h_1124 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_1132 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_1125 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_1124)
                )
            )
          let _object_h1133 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124)))
          have h_1133 : Litex.In _value_i2 _object_h1133 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124) _object_h1133 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124)) h_1132)
                )
            )
          have h_1134 : Litex.Same (Litex.matrixDiagonal _value_i2 _value_i1 h_1124 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124)
            exact h_1132)) (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
            have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) _raw_i5 _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
              intro _raw_i5 _raw_i6 h_1497 h_1502 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1497)
              have h_1497 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1497
              have h_1498 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).1
                    )
                )
              have h_1499 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.1
                    )
                )
              have h_1500 : Litex.Le _value_i5 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.2
                    )
                )
              have h_1501 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1497)
                    )
                )
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1502)
              have h_1502 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1502
              have h_1503 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).1
                    )
                )
              have h_1504 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.1
                    )
                )
              have h_1505 : Litex.Le _value_i6 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.2
                    )
                )
              have h_1506 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1502)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_3_1 := (let _setElement_0 := _value_i6;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_3_0 _wd_3_1));
                (Litex.finiteSetSize _wd_2_0 (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i6;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))));
                let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                  exact h_1497) True.intro);
                (Litex.mul _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i6;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1));
                  (Litex.finiteSetSize _wd_2_0 (by
                    let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    let _wd_3_1 := (let _setElement_0 := _value_i6;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (Litex.intersect _wd_3_0 _wd_3_1))
                    exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0)) (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0))))))
                  exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                  let _atomic_wd_2_0 := _wd_1_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_3_1 := (let _setElement_0 := _value_i6;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_3_0 _wd_3_1));
                (Litex.finiteSetSize _wd_2_0 (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i6;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))));
                let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                  exact h_1497) True.intro);
                (Litex.mul _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i6;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1));
                  (Litex.finiteSetSize _wd_2_0 (by
                    let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    let _wd_3_1 := (let _setElement_0 := _value_i6;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (Litex.intersect _wd_3_0 _wd_3_1))
                    exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0)) (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0))))))
                  exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                  let _atomic_wd_2_0 := _wd_1_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact (by
                  let _arithmetic := _atomic_wd_1_0
                  exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
            exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _pointwise : ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_3793 : Litex.In _value_i14 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_3798 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (by
                      let _object_w37 := (let _litex_matrix_head := (Litex.matrixDiagonal _value_i2 _value_i1 h_1124 (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124)
                        exact h_1132));
                      (let _litex_call_arg_0 := _value_i14;
                      let _litex_call_arg_1 := _value_i15;
                      Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.order (_litex_matrix_head).val.order .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixDiagonalInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                        exact h_3793) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                        exact h_3798)), True.intro⟩)))
                      let _object_w38 := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                        have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) _raw_i5 _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                          intro _raw_i5 _raw_i6 h_5585 h_5590 _
                          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_5585)
                          have h_5585 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_5585
                          have h_5586 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_5585).1
                                )
                            )
                          have h_5587 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_5585).2.1
                                )
                            )
                          have h_5588 : Litex.Le _value_i5 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_5585).2.2
                                )
                            )
                          have h_5589 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5585)
                                )
                            )
                          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_5590)
                          have h_5590 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_5590
                          have h_5591 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_5590).1
                                )
                            )
                          have h_5592 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_5590).2.1
                                )
                            )
                          have h_5593 : Litex.Le _value_i6 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_5590).2.2
                                )
                            )
                          have h_5594 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5590)
                                )
                            )
                          change (by
                            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_4_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_4_0 _wd_4_1));
                            (Litex.finiteSetSize _wd_3_0 (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_4_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_4_0 _wd_4_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))));
                            let _wd_2_1 := (let _litex_call_arg_0 := _value_i5;
                            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                              exact h_5585) True.intro);
                            (Litex.mul _wd_2_0 _wd_2_1 (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_4_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_4_0 _wd_4_1));
                              (Litex.finiteSetSize _wd_3_0 (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0);
                                let _wd_4_1 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0);
                                (Litex.intersect _wd_4_0 _wd_4_1))
                                exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                  let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                    let _setTail_1 := Litex.emptySet (M := M);
                                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                    _setTail_0)
                                  exact (let _finite_tail_0 := _atomic_wd_4_0;
                                  let _finite_tail_1 := _finite_tail_0.val.tail;
                                  have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                  _finite_0)) (by
                                  let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                    let _setTail_1 := Litex.emptySet (M := M);
                                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                    _setTail_0)
                                  exact (let _finite_tail_0 := _atomic_wd_4_0;
                                  let _finite_tail_1 := _finite_tail_0.val.tail;
                                  have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                  _finite_0))))))
                              exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                              let _atomic_wd_2_0 := _wd_2_1
                              exact (by
                                let _litex_return_call := _atomic_wd_2_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                          exact (by
                            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_4_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_4_0 _wd_4_1));
                            (Litex.finiteSetSize _wd_3_0 (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_4_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_4_0 _wd_4_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))));
                            let _wd_2_1 := (let _litex_call_arg_0 := _value_i5;
                            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                              exact h_5585) True.intro);
                            (Litex.mul _wd_2_0 _wd_2_1 (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_4_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_4_0 _wd_4_1));
                              (Litex.finiteSetSize _wd_3_0 (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0);
                                let _wd_4_1 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0);
                                (Litex.intersect _wd_4_0 _wd_4_1))
                                exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                  let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                    let _setTail_1 := Litex.emptySet (M := M);
                                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                    _setTail_0)
                                  exact (let _finite_tail_0 := _atomic_wd_4_0;
                                  let _finite_tail_1 := _finite_tail_0.val.tail;
                                  have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                  _finite_0)) (by
                                  let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                    let _setTail_1 := Litex.emptySet (M := M);
                                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                    _setTail_0)
                                  exact (let _finite_tail_0 := _atomic_wd_4_0;
                                  let _finite_tail_1 := _finite_tail_0.val.tail;
                                  have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                  _finite_0))))))
                              exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                              let _atomic_wd_2_0 := _wd_2_1
                              exact (by
                                let _litex_return_call := _atomic_wd_2_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (by
                              let _arithmetic := _atomic_wd_1_0
                              exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                        intro _litex_input _litex_domain
                        obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                        exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
                      let _wd_1_1 := _value_i14;
                      let _wd_1_2 := _value_i15;
                      (let _litex_call_arg_0 := _wd_1_1;
                      let _litex_call_arg_1 := _wd_1_2;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                        exact h_3793) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                        exact h_3798)) True.intro))
                      exact (by
                        let _equal_wd_1_0 := _object_w37
                        let _equal_wd_1_1 := _object_w38
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
                    ) := (by
                      intro _Host_i14 _rep_i14 _value_i14 h_3793 _Host_i15 _rep_i15 _value_i15 h_3798
                      have h_3794 : Litex.In _value_i14 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i14 h_3793).1
                            )
                        )
                      have h_3795 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i14 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i14 h_3793).2.1
                            )
                        )
                      have h_3796 : Litex.Le _value_i14 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i14 h_3793).2.2
                            )
                        )
                      have h_3797 : Litex.In _value_i14 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i14 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3793)
                            )
                        )
                      have h_3799 : Litex.In _value_i15 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i15 h_3798).1
                            )
                        )
                      have h_3800 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i15 h_3798).2.1
                            )
                        )
                      have h_3801 : Litex.Le _value_i15 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i15 h_3798).2.2
                            )
                        )
                      have h_3802 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3798)
                            )
                        )
                      let _object_w37 := (let _litex_matrix_head := (Litex.matrixDiagonal _value_i2 _value_i1 h_1124 (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124)
                        exact h_1132));
                      (let _litex_call_arg_0 := _value_i14;
                      let _litex_call_arg_1 := _value_i15;
                      Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.order (_litex_matrix_head).val.order .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixDiagonalInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                        exact h_3793) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                        exact h_3798)), True.intro⟩)))
                      let _object_w38 := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                        have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) _raw_i5 _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                          intro _raw_i5 _raw_i6 h_5585 h_5590 _
                          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_5585)
                          have h_5585 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_5585
                          have h_5586 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_5585).1
                                )
                            )
                          have h_5587 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_5585).2.1
                                )
                            )
                          have h_5588 : Litex.Le _value_i5 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_5585).2.2
                                )
                            )
                          have h_5589 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5585)
                                )
                            )
                          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_5590)
                          have h_5590 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_5590
                          have h_5591 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_5590).1
                                )
                            )
                          have h_5592 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_5590).2.1
                                )
                            )
                          have h_5593 : Litex.Le _value_i6 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_5590).2.2
                                )
                            )
                          have h_5594 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5590)
                                )
                            )
                          change (by
                            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_4_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_4_0 _wd_4_1));
                            (Litex.finiteSetSize _wd_3_0 (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_4_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_4_0 _wd_4_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))));
                            let _wd_2_1 := (let _litex_call_arg_0 := _value_i5;
                            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                              exact h_5585) True.intro);
                            (Litex.mul _wd_2_0 _wd_2_1 (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_4_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_4_0 _wd_4_1));
                              (Litex.finiteSetSize _wd_3_0 (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0);
                                let _wd_4_1 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0);
                                (Litex.intersect _wd_4_0 _wd_4_1))
                                exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                  let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                    let _setTail_1 := Litex.emptySet (M := M);
                                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                    _setTail_0)
                                  exact (let _finite_tail_0 := _atomic_wd_4_0;
                                  let _finite_tail_1 := _finite_tail_0.val.tail;
                                  have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                  _finite_0)) (by
                                  let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                    let _setTail_1 := Litex.emptySet (M := M);
                                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                    _setTail_0)
                                  exact (let _finite_tail_0 := _atomic_wd_4_0;
                                  let _finite_tail_1 := _finite_tail_0.val.tail;
                                  have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                  _finite_0))))))
                              exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                              let _atomic_wd_2_0 := _wd_2_1
                              exact (by
                                let _litex_return_call := _atomic_wd_2_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                          exact (by
                            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_4_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_4_0 _wd_4_1));
                            (Litex.finiteSetSize _wd_3_0 (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_4_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_4_0 _wd_4_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))));
                            let _wd_2_1 := (let _litex_call_arg_0 := _value_i5;
                            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                              exact h_5585) True.intro);
                            (Litex.mul _wd_2_0 _wd_2_1 (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_4_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_4_0 _wd_4_1));
                              (Litex.finiteSetSize _wd_3_0 (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0);
                                let _wd_4_1 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0);
                                (Litex.intersect _wd_4_0 _wd_4_1))
                                exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                  let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                    let _setTail_1 := Litex.emptySet (M := M);
                                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                    _setTail_0)
                                  exact (let _finite_tail_0 := _atomic_wd_4_0;
                                  let _finite_tail_1 := _finite_tail_0.val.tail;
                                  have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                  _finite_0)) (by
                                  let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                    let _setTail_1 := Litex.emptySet (M := M);
                                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                    _setTail_0)
                                  exact (let _finite_tail_0 := _atomic_wd_4_0;
                                  let _finite_tail_1 := _finite_tail_0.val.tail;
                                  have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                  _finite_0))))))
                              exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                              let _atomic_wd_2_0 := _wd_2_1
                              exact (by
                                let _litex_return_call := _atomic_wd_2_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (by
                              let _arithmetic := _atomic_wd_1_0
                              exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                        intro _litex_input _litex_domain
                        obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                        exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
                      let _wd_1_1 := _value_i14;
                      let _wd_1_2 := _value_i15;
                      (let _litex_call_arg_0 := _wd_1_1;
                      let _litex_call_arg_1 := _wd_1_2;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                        exact h_3793) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                        exact h_3798)) True.intro))
                      have h_3467 : (by
                        let _equal_wd_1_0 := _object_w37
                        let _equal_wd_1_1 := _object_w38
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (let _equal_wd_1_0 := _object_w37;
                              let _equal_wd_1_1 := _object_w38;
                              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((let _matrix_beta_call := _equal_wd_1_0;
                                (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_equal_wd_1_0).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (Litex.denote _value_i15)])) = Litex.denote _matrix_beta_call from rfl).trans ((show Litex.denote _matrix_beta_call = (M.mulValue (Litex.matrixIdentityEntry (Litex.denote _value_i14) (Litex.denote _value_i15)) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.vector) (Litex.denote _value_i14))) from by
                                have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i14 _value_i15))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixDiagonalCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i14 _value_i15)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              ))) (fun (_litex_input : M.Value) => (fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i14 _value_i15))).mpr ⟨(Litex.callArguments2_mem_cart _value_i14 _value_i15 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                                exact h_3793) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                                exact h_3798)), True.intro⟩))
                                change Litex.denote _matrix_beta_call = Litex.matrixDiagonalBody (Litex.denote ((_equal_wd_1_0).val.function).val.vector) (Litex.FiniteFunction.pack2 (Litex.denote _value_i14) (Litex.denote _value_i15)) at h
                                dsimp only [Litex.matrixDiagonalBody] at h
                                rw [Litex.FiniteFunction.unpack_pack2] at h
                                exact h).trans (show (M.mulValue (Litex.matrixIdentityEntry (Litex.denote _value_i14) (Litex.denote _value_i15)) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.vector) (Litex.denote _value_i14))) = (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i14) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i15) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.denote _value_i14))) from rfl)))).trans (((Eq.refl (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i14) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i15) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.denote _value_i14))))).trans ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (Litex.denote _value_i15)])) = (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i14) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i15) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.denote _value_i14))) from by
                                let _litex_original := _equal_wd_1_1
                                let _litex_formula := _litex_original.val.function
                                have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := rfl
                                have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
                                have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) _litex_original.wd.2
                                exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_original.val.argument) = (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i14) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i15) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.denote _value_i14))); exact (congrArg₂ (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i14), (Litex.denote _value_i15)]) (M.number (1 : ℂ)) = (Litex.denote _value_i14) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i14), (Litex.denote _value_i15)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i14), (Litex.denote _value_i15)]) (M.number (2 : ℂ)) = (Litex.denote _value_i15) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i14), (Litex.denote _value_i15)] (1 : Fin 2)))))
                              )).symm))))
                            )
                        )
                      exact h_3467
                    )
                    apply Litex.functionExtOnDomain (Litex.matrixDiagonal _value_i2 _value_i1 h_1124 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124)
                      exact h_1132)) (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) _raw_i5 _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                        intro _raw_i5 _raw_i6 h_1497 h_1502 _
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1497)
                        have h_1497 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1497
                        have h_1498 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).1
                              )
                          )
                        have h_1499 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.1
                              )
                          )
                        have h_1500 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.2
                              )
                          )
                        have h_1501 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1497)
                              )
                          )
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1502)
                        have h_1502 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1502
                        have h_1503 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).1
                              )
                          )
                        have h_1504 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.1
                              )
                          )
                        have h_1505 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.2
                              )
                          )
                        have h_1506 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1502)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_matrix := (Litex.matrixDiagonal _value_i2 _value_i1 h_1124 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124)
                      exact h_1132)); let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixDiagonalInFnSet _litex_matrix)) (Litex.inOfSame (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) _raw_i5 _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                        intro _raw_i5 _raw_i6 h_1497 h_1502 _
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1497)
                        have h_1497 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1497
                        have h_1498 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).1
                              )
                          )
                        have h_1499 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.1
                              )
                          )
                        have h_1500 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.2
                              )
                          )
                        have h_1501 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1497)
                              )
                          )
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1502)
                        have h_1502 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1502
                        have h_1503 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).1
                              )
                          )
                        have h_1504 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.1
                              )
                          )
                        have h_1505 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.2
                              )
                          )
                        have h_1506 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1502)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) _raw_i5 _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                        intro _raw_i5 _raw_i6 h_1497 h_1502 _
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1497)
                        have h_1497 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1497
                        have h_1498 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).1
                              )
                          )
                        have h_1499 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.1
                              )
                          )
                        have h_1500 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.2
                              )
                          )
                        have h_1501 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1497)
                              )
                          )
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1502)
                        have h_1502 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1502
                        have h_1503 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).1
                              )
                          )
                        have h_1504 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.1
                              )
                          )
                        have h_1505 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.2
                              )
                          )
                        have h_1506 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1502)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) (Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) _raw_i5 _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                        intro _raw_i5 _raw_i6 h_1497 h_1502 _
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1497)
                        have h_1497 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1497
                        have h_1498 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).1
                              )
                          )
                        have h_1499 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.1
                              )
                          )
                        have h_1500 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.2
                              )
                          )
                        have h_1501 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1497)
                              )
                          )
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1502)
                        have h_1502 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1502
                        have h_1503 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).1
                              )
                          )
                        have h_1504 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.1
                              )
                          )
                        have h_1505 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.2
                              )
                          )
                        have h_1506 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1502)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)))) (by rfl)
                    intro _preimage_input _preimage_domain
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                      have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                      have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))
                    have _repack : _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) := (by
                      apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                      apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                      funext i
                      fin_cases i <;> norm_num [Litex.FiniteFunction.index])
                    exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.matrixDiagonal _value_i2 _value_i1 h_1124 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124)
                      exact h_1132))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) _raw_i5 _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                        intro _raw_i5 _raw_i6 h_1497 h_1502 _
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1497)
                        have h_1497 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1497
                        have h_1498 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).1
                              )
                          )
                        have h_1499 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.1
                              )
                          )
                        have h_1500 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.2
                              )
                          )
                        have h_1501 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1497)
                              )
                          )
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1502)
                        have h_1502 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1502
                        have h_1503 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).1
                              )
                          )
                        have h_1504 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.1
                              )
                          )
                        have h_1505 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.2
                              )
                          )
                        have h_1506 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1502)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_3_1 := (let _setElement_0 := _value_i6;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_3_0 _wd_3_1));
                          (Litex.finiteSetSize _wd_2_0 (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))));
                          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                            exact h_1497) True.intro);
                          (Litex.mul _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i6;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i6;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_4_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))) x) _repack) (_pointwise (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))
                  )
                )
            )
          exact (let _equal_wd_1_0 := (Litex.matrixDiagonal _value_i2 _value_i1 h_1124 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_1124)
            exact h_1132));
          let _equal_wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i3 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
            have _litex_checked_return : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → M.mem ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i3 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3))) _raw_i3 _raw_i4) (Litex.denote (Litex.C (M := M))) := (by
              intro _raw_i3 _raw_i4 h_11300 h_11305 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11300)
              have h_11300 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_11300
              have h_11301 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i3 h_11300).1
                    )
                )
              have h_11302 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i3 h_11300).2.1
                    )
                )
              have h_11303 : Litex.Le _value_i3 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i3 h_11300).2.2
                    )
                )
              have h_11304 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_11300)
                    )
                )
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11305)
              have h_11305 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_11305
              have h_11306 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i4 h_11305).1
                    )
                )
              have h_11307 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i4 h_11305).2.1
                    )
                )
              have h_11308 : Litex.Le _value_i4 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i4 h_11305).2.2
                    )
                )
              have h_11309 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_11305)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_3_1 := (let _setElement_0 := _value_i4;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_3_0 _wd_3_1));
                (Litex.finiteSetSize _wd_2_0 (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i4;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i3;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))));
                let _wd_1_1 := (let _litex_call_arg_0 := _value_i3;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                  exact h_11300) True.intro);
                (Litex.mul _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i4;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1));
                  (Litex.finiteSetSize _wd_2_0 (by
                    let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    let _wd_3_1 := (let _setElement_0 := _value_i4;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (Litex.intersect _wd_3_0 _wd_3_1))
                    exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i3;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0)) (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i4;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0))))))
                  exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                  let _atomic_wd_2_0 := _wd_1_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_3_1 := (let _setElement_0 := _value_i4;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_3_0 _wd_3_1));
                (Litex.finiteSetSize _wd_2_0 (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i4;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i3;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))));
                let _wd_1_1 := (let _litex_call_arg_0 := _value_i3;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                  exact h_11300) True.intro);
                (Litex.mul _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i4;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1));
                  (Litex.finiteSetSize _wd_2_0 (by
                    let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    let _wd_3_1 := (let _setElement_0 := _value_i4;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (Litex.intersect _wd_3_0 _wd_3_1))
                    exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i3;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0)) (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i4;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0))))))
                  exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                  let _atomic_wd_2_0 := _wd_1_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact (by
                  let _arithmetic := _atomic_wd_1_0
                  exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
            exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_1134).trans (by
            let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
            have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i6 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i5))) _raw_i5 _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
              intro _raw_i5 _raw_i6 h_1497 h_1502 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1497)
              have h_1497 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1497
              have h_1498 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).1
                    )
                )
              have h_1499 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.1
                    )
                )
              have h_1500 : Litex.Le _value_i5 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 h_1497).2.2
                    )
                )
              have h_1501 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1497)
                    )
                )
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1502)
              have h_1502 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) := h_1502
              have h_1503 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).1
                    )
                )
              have h_1504 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.1
                    )
                )
              have h_1505 : Litex.Le _value_i6 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 h_1502).2.2
                    )
                )
              have h_1506 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1502)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_3_1 := (let _setElement_0 := _value_i6;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_3_0 _wd_3_1));
                (Litex.finiteSetSize _wd_2_0 (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i6;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))));
                let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                  exact h_1497) True.intro);
                (Litex.mul _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i6;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1));
                  (Litex.finiteSetSize _wd_2_0 (by
                    let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    let _wd_3_1 := (let _setElement_0 := _value_i6;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (Litex.intersect _wd_3_0 _wd_3_1))
                    exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0)) (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0))))))
                  exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                  let _atomic_wd_2_0 := _wd_1_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_3_1 := (let _setElement_0 := _value_i6;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_3_0 _wd_3_1));
                (Litex.finiteSetSize _wd_2_0 (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i6;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i6;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))));
                let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_1133 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))
                  exact h_1497) True.intro);
                (Litex.mul _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_3_1 := (let _setElement_0 := _value_i6;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_3_0 _wd_3_1));
                  (Litex.finiteSetSize _wd_2_0 (by
                    let _atomic_wd_3_0 := (let _wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    let _wd_3_1 := (let _setElement_0 := _value_i6;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (Litex.intersect _wd_3_0 _wd_3_1))
                    exact (Litex.finiteSetIntersect _atomic_wd_3_0 (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i5;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0)) (by
                      let _atomic_wd_4_0 := (let _setElement_0 := _value_i6;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (let _finite_tail_0 := _atomic_wd_4_0;
                      let _finite_tail_1 := _finite_tail_0.val.tail;
                      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                      _finite_0))))))
                  exact (Litex.naturalToComplex _atomic_wd_2_0 (Litex.finiteSetSizeInN _atomic_wd_2_0))) (by
                  let _atomic_wd_2_0 := _wd_1_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact (by
                  let _arithmetic := _atomic_wd_1_0
                  exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_1124)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
            exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
            let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_1_1
            exact (show Litex.Same _left _right from rfl))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_diagonal_x5f_formula_x2f_statement_x2e_lit
