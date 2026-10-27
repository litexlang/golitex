import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_diagonal_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_24 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_32 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_24)) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_57 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_62 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))), (by
  let _object_h33 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_24)))
  have h_33 : Litex.In _value_i2 _object_h33 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_24) _object_h33 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_24)) h_32)
        )
    )
  let _object_w9 := (let _litex_matrix_head := (Litex.matrixDiagonal _value_i2 _value_i1 h_24 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_24)
    exact h_32));
  (let _litex_call_arg_0 := _value_i3;
  let _litex_call_arg_1 := _value_i4;
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.order (_litex_matrix_head).val.order .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixDiagonalInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))
    exact h_57) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))
    exact h_62)), True.intro⟩)))
  let _object_w10 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
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
    let _atomic_wd_1_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
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
    exact (Litex.finiteSetIntersect _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := (let _setElement_0 := _value_i3;
        let _setTail_1 := Litex.emptySet (M := M);
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0)
      exact (let _finite_tail_0 := _atomic_wd_2_0;
      let _finite_tail_1 := _finite_tail_0.val.tail;
      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
      _finite_0)) (by
      let _atomic_wd_2_0 := (let _setElement_0 := _value_i4;
        let _setTail_1 := Litex.emptySet (M := M);
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0)
      exact (let _finite_tail_0 := _atomic_wd_2_0;
      let _finite_tail_1 := _finite_tail_0.val.tail;
      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
      _finite_0))))));
  let _wd_1_1 := (let _litex_call_arg_0 := _value_i3;
  Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_33 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))
    exact h_57) True.intro);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
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
        _finite_0))))))
    exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
  exact (by
    let _equal_wd_1_0 := _object_w9
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_24 _Host_i2 _rep_i2 _value_i2 h_32 _Host_i3 _rep_i3 _value_i3 h_57 _Host_i4 _rep_i4 _value_i4 h_62
          have h_25 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_24)
                )
            )
          let _object_h33 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_24)))
          have h_33 : Litex.In _value_i2 _object_h33 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_24) _object_h33 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_24)) h_32)
                )
            )
          have h_58 : Litex.In _value_i3 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) _value_i3 h_57).1
                )
            )
          have h_59 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) _value_i3 h_57).2.1
                )
            )
          have h_60 : Litex.Le _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) _value_i3 h_57).2.2
                )
            )
          have h_61 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_57)
                )
            )
          have h_63 : Litex.In _value_i4 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) _value_i4 h_62).1
                )
            )
          have h_64 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) _value_i4 h_62).2.1
                )
            )
          have h_65 : Litex.Le _value_i4 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) _value_i4 h_62).2.2
                )
            )
          have h_66 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_62)
                )
            )
          let _object_w9 := (let _litex_matrix_head := (Litex.matrixDiagonal _value_i2 _value_i1 h_24 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_24)
            exact h_32));
          (let _litex_call_arg_0 := _value_i3;
          let _litex_call_arg_1 := _value_i4;
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.order (_litex_matrix_head).val.order .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixDiagonalInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))
            exact h_57) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))
            exact h_62)), True.intro⟩)))
          let _object_w10 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
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
            let _atomic_wd_1_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
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
            exact (Litex.finiteSetIntersect _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := (let _setElement_0 := _value_i3;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (let _finite_tail_0 := _atomic_wd_2_0;
              let _finite_tail_1 := _finite_tail_0.val.tail;
              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
              _finite_0)) (by
              let _atomic_wd_2_0 := (let _setElement_0 := _value_i4;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (let _finite_tail_0 := _atomic_wd_2_0;
              let _finite_tail_1 := _finite_tail_0.val.tail;
              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
              _finite_0))))));
          let _wd_1_1 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_33 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))
            exact h_57) True.intro);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i3;
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
                _finite_0))))))
            exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w9;
                  let _equal_wd_1_1 := _object_w10;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((let _matrix_beta_call := _equal_wd_1_0;
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_equal_wd_1_0).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i4)])) = Litex.denote _matrix_beta_call from rfl).trans ((show Litex.denote _matrix_beta_call = (M.mulValue (Litex.matrixIdentityEntry (Litex.denote _value_i3) (Litex.denote _value_i4)) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.vector) (Litex.denote _value_i3))) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i3 _value_i4))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixDiagonalCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i3 _value_i4)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i3 _value_i4))).mpr ⟨(Litex.callArguments2_mem_cart _value_i3 _value_i4 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))
                    exact h_57) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_24))
                    exact h_62)), True.intro⟩))
                    change Litex.denote _matrix_beta_call = Litex.matrixDiagonalBody (Litex.denote ((_equal_wd_1_0).val.function).val.vector) (Litex.FiniteFunction.pack2 (Litex.denote _value_i3) (Litex.denote _value_i4)) at h
                    dsimp only [Litex.matrixDiagonalBody] at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (show (M.mulValue (Litex.matrixIdentityEntry (Litex.denote _value_i3) (Litex.denote _value_i4)) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.vector) (Litex.denote _value_i3))) = (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i3) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i4) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.denote _value_i3))) from rfl)))).trans (Eq.refl (M.mulValue (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i3) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i4) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.denote _value_i3)))))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_diagonal_x5f_coordinates_x2f_statement_x2e_lit
