import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_matrix_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_21 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_36 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_41 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21))), (by
  let _object_w7 := (let _litex_matrix_head := (Litex.identityMatrix _value_i1 h_21);
  (let _litex_call_arg_0 := _value_i2;
  let _litex_call_arg_1 := _value_i3;
  Litex.callOn (Litex.identityMatrixSignature (_litex_matrix_head).val.order) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.identityMatrixInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21))
    exact h_36) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21))
    exact h_41)), True.intro⟩)))
  let _object_w8 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_2_1 := (let _setElement_0 := _value_i3;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.intersect _wd_2_0 _wd_2_1));
  (Litex.finiteSetSize _wd_1_0 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    let _wd_2_1 := (let _setElement_0 := _value_i3;
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    (Litex.intersect _wd_2_0 _wd_2_1))
    exact (Litex.finiteSetIntersect _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := (let _setElement_0 := _value_i2;
        let _setTail_1 := Litex.emptySet (M := M);
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0)
      exact (let _finite_tail_0 := _atomic_wd_2_0;
      let _finite_tail_1 := _finite_tail_0.val.tail;
      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
      _finite_0)) (by
      let _atomic_wd_2_0 := (let _setElement_0 := _value_i3;
        let _setTail_1 := Litex.emptySet (M := M);
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0)
      exact (let _finite_tail_0 := _atomic_wd_2_0;
      let _finite_tail_1 := _finite_tail_0.val.tail;
      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
      _finite_0))))))
  exact (by
    let _equal_wd_1_0 := _object_w7
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_21 _Host_i2 _rep_i2 _value_i2 h_36 _Host_i3 _rep_i3 _value_i3 h_41
          have h_22 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_21)
                )
            )
          have h_37 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)) _value_i2 h_36).1
                )
            )
          have h_38 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)) _value_i2 h_36).2.1
                )
            )
          have h_39 : Litex.Le _value_i2 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)) _value_i2 h_36).2.2
                )
            )
          have h_40 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_36)
                )
            )
          have h_42 : Litex.In _value_i3 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)) _value_i3 h_41).1
                )
            )
          have h_43 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)) _value_i3 h_41).2.1
                )
            )
          have h_44 : Litex.Le _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)) _value_i3 h_41).2.2
                )
            )
          have h_45 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_41)
                )
            )
          let _object_w7 := (let _litex_matrix_head := (Litex.identityMatrix _value_i1 h_21);
          (let _litex_call_arg_0 := _value_i2;
          let _litex_call_arg_1 := _value_i3;
          Litex.callOn (Litex.identityMatrixSignature (_litex_matrix_head).val.order) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.identityMatrixInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21))
            exact h_36) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21))
            exact h_41)), True.intro⟩)))
          let _object_w8 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := _value_i3;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.intersect _wd_2_0 _wd_2_1));
          (Litex.finiteSetSize _wd_1_0 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_2_1 := (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.intersect _wd_2_0 _wd_2_1))
            exact (Litex.finiteSetIntersect _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := (let _setElement_0 := _value_i2;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (let _finite_tail_0 := _atomic_wd_2_0;
              let _finite_tail_1 := _finite_tail_0.val.tail;
              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
              _finite_0)) (by
              let _atomic_wd_2_0 := (let _setElement_0 := _value_i3;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (let _finite_tail_0 := _atomic_wd_2_0;
              let _finite_tail_1 := _finite_tail_0.val.tail;
              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
              _finite_0))))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w7
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w7;
                  let _equal_wd_1_1 := _object_w8;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((let _matrix_beta_call := _equal_wd_1_0;
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_equal_wd_1_0).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i2), (Litex.denote _value_i3)])) = Litex.denote _matrix_beta_call from rfl).trans ((show Litex.denote _matrix_beta_call = (Litex.matrixIdentityEntry (Litex.denote _value_i2) (Litex.denote _value_i3)) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i2 _value_i3))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.identityMatrixCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i2 _value_i3)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i2 _value_i3))).mpr ⟨(Litex.callArguments2_mem_cart _value_i2 _value_i3 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21))
                    exact h_36) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_21))
                    exact h_41)), True.intro⟩))
                    change Litex.denote _matrix_beta_call = Litex.matrixIdentityBody (Litex.FiniteFunction.pack2 (Litex.denote _value_i2) (Litex.denote _value_i3)) at h
                    dsimp only [Litex.matrixIdentityBody] at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (show (Litex.matrixIdentityEntry (Litex.denote _value_i2) (Litex.denote _value_i3)) = (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i2) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i3) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) from rfl)))).trans (Eq.refl (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i2) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i3) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_matrix_x5f_coordinates_x2f_statement_x2e_lit
