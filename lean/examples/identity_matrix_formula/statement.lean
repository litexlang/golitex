import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_matrix_x5f_formula_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.N (M := M))), (by
  let _equal_wd_1_0 := (Litex.identityMatrix _value_i1 h_4)
  let _equal_wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i2 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i3 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
    have _litex_checked_return : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))) → M.mem _raw_i3 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i2 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i3 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i2 _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
      intro _raw_i2 _raw_i3 h_221 h_226 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_221)
      have h_221 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) := h_221
      have h_222 : Litex.In _value_i2 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i2 h_221).1
            )
        )
      have h_223 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i2 h_221).2.1
            )
        )
      have h_224 : Litex.Le _value_i2 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i2 h_221).2.2
            )
        )
      have h_225 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_221)
            )
        )
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_226)
      have h_226 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) := h_226
      have h_227 : Litex.In _value_i3 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i3 h_226).1
            )
        )
      have h_228 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i3 h_226).2.1
            )
        )
      have h_229 : Litex.Le _value_i3 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i3 h_226).2.2
            )
        )
      have h_230 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_226)
            )
        )
      change (by
        let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
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
          let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
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
          exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
            let _atomic_wd_3_0 := (let _setElement_0 := _value_i2;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_3_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0)) (by
            let _atomic_wd_3_0 := (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_3_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0))))))
        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
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
          let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
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
          exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
            let _atomic_wd_3_0 := (let _setElement_0 := _value_i2;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_3_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0)) (by
            let _atomic_wd_3_0 := (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_3_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0))))))
        exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
    intro _litex_input _litex_domain
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_4)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
    exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4
          have h_5 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_4)
                )
            )
          have h_267 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_268 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_267)
                )
            )
          have h_269 : Litex.Same (Litex.identityMatrix _value_i1 h_267) (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
            have _litex_checked_return : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i4 _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i4 _raw_i5 h_485 h_490 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_485)
              have h_485 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_485
              have h_486 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).1
                    )
                )
              have h_487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.1
                    )
                )
              have h_488 : Litex.Le _value_i4 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.2
                    )
                )
              have h_489 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_485)
                    )
                )
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_490)
              have h_490 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_490
              have h_491 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).1
                    )
                )
              have h_492 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.1
                    )
                )
              have h_493 : Litex.Le _value_i5 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.2
                    )
                )
              have h_494 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_490)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_2_1 := (let _setElement_0 := _value_i5;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_2_0 _wd_2_1));
                (Litex.finiteSetSize _wd_1_0 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_2_1 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_2_0 _wd_2_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))))
                exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_2_1 := (let _setElement_0 := _value_i5;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_2_0 _wd_2_1));
                (Litex.finiteSetSize _wd_1_0 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_2_1 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_2_0 _wd_2_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))))
                exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
            exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _pointwise : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_774 : Litex.In _value_i9 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_779 : Litex.In _value_i10 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (by
                      let _object_w21 := (let _litex_matrix_head := (Litex.identityMatrix _value_i1 h_267);
                      (let _litex_call_arg_0 := _value_i9;
                      let _litex_call_arg_1 := _value_i10;
                      Litex.callOn (Litex.identityMatrixSignature (_litex_matrix_head).val.order) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.identityMatrixInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                        exact h_774) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                        exact h_779)), True.intro⟩)))
                      let _object_w22 := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                        have _litex_checked_return : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i4 _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                          intro _raw_i4 _raw_i5 h_853 h_858 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_853)
                          have h_853 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_853
                          have h_854 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_853).1
                                )
                            )
                          have h_855 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_853).2.1
                                )
                            )
                          have h_856 : Litex.Le _value_i4 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_853).2.2
                                )
                            )
                          have h_857 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_853)
                                )
                            )
                          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_858)
                          have h_858 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_858
                          have h_859 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_858).1
                                )
                            )
                          have h_860 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_858).2.1
                                )
                            )
                          have h_861 : Litex.Le _value_i5 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_858).2.2
                                )
                            )
                          have h_862 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_858)
                                )
                            )
                          change (by
                            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                          exact (by
                            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
                        intro _litex_input _litex_domain
                        obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                        exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
                      let _wd_1_1 := _value_i9;
                      let _wd_1_2 := _value_i10;
                      (let _litex_call_arg_0 := _wd_1_1;
                      let _litex_call_arg_1 := _wd_1_2;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                        exact h_774) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                        exact h_779)) True.intro))
                      exact (by
                        let _equal_wd_1_0 := _object_w21
                        let _equal_wd_1_1 := _object_w22
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
                    ) := (by
                      intro _Host_i9 _rep_i9 _value_i9 h_774 _Host_i10 _rep_i10 _value_i10 h_779
                      have h_775 : Litex.In _value_i9 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i9 h_774).1
                            )
                        )
                      have h_776 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i9 h_774).2.1
                            )
                        )
                      have h_777 : Litex.Le _value_i9 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i9 h_774).2.2
                            )
                        )
                      have h_778 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_774)
                            )
                        )
                      have h_780 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i10 h_779).1
                            )
                        )
                      have h_781 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i10 h_779).2.1
                            )
                        )
                      have h_782 : Litex.Le _value_i10 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i10 h_779).2.2
                            )
                        )
                      have h_783 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_779)
                            )
                        )
                      let _object_w21 := (let _litex_matrix_head := (Litex.identityMatrix _value_i1 h_267);
                      (let _litex_call_arg_0 := _value_i9;
                      let _litex_call_arg_1 := _value_i10;
                      Litex.callOn (Litex.identityMatrixSignature (_litex_matrix_head).val.order) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.identityMatrixInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                        exact h_774) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                        exact h_779)), True.intro⟩)))
                      let _object_w22 := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                        have _litex_checked_return : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i4 _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                          intro _raw_i4 _raw_i5 h_853 h_858 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_853)
                          have h_853 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_853
                          have h_854 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_853).1
                                )
                            )
                          have h_855 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_853).2.1
                                )
                            )
                          have h_856 : Litex.Le _value_i4 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_853).2.2
                                )
                            )
                          have h_857 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_853)
                                )
                            )
                          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_858)
                          have h_858 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_858
                          have h_859 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_858).1
                                )
                            )
                          have h_860 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_858).2.1
                                )
                            )
                          have h_861 : Litex.Le _value_i5 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_858).2.2
                                )
                            )
                          have h_862 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_858)
                                )
                            )
                          change (by
                            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                          exact (by
                            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_3_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_3_0 _wd_3_1));
                            (Litex.finiteSetSize _wd_2_0 (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              let _wd_3_1 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0);
                              (Litex.intersect _wd_3_0 _wd_3_1))
                              exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0)) (by
                                let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact (let _finite_tail_0 := _atomic_wd_3_0;
                                let _finite_tail_1 := _finite_tail_0.val.tail;
                                have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                                have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                                _finite_0))))))
                            exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
                        intro _litex_input _litex_domain
                        obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                        exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
                      let _wd_1_1 := _value_i9;
                      let _wd_1_2 := _value_i10;
                      (let _litex_call_arg_0 := _wd_1_1;
                      let _litex_call_arg_1 := _wd_1_2;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                        exact h_774) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                        exact h_779)) True.intro))
                      have h_578 : (by
                        let _equal_wd_1_0 := _object_w21
                        let _equal_wd_1_1 := _object_w22
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (let _equal_wd_1_0 := _object_w21;
                              let _equal_wd_1_1 := _object_w22;
                              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((let _matrix_beta_call := _equal_wd_1_0;
                                (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_equal_wd_1_0).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = Litex.denote _matrix_beta_call from rfl).trans ((show Litex.denote _matrix_beta_call = (Litex.matrixIdentityEntry (Litex.denote _value_i9) (Litex.denote _value_i10)) from by
                                have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i9 _value_i10))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.identityMatrixCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i9 _value_i10)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              ))) (fun (_litex_input : M.Value) => (fun (_raw_i19 : M.Value) (_raw_i20 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i9 _value_i10))).mpr ⟨(Litex.callArguments2_mem_cart _value_i9 _value_i10 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                                exact h_774) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))
                                exact h_779)), True.intro⟩))
                                change Litex.denote _matrix_beta_call = Litex.matrixIdentityBody (Litex.FiniteFunction.pack2 (Litex.denote _value_i9) (Litex.denote _value_i10)) at h
                                dsimp only [Litex.matrixIdentityBody] at h
                                rw [Litex.FiniteFunction.unpack_pack2] at h
                                exact h).trans (show (Litex.matrixIdentityEntry (Litex.denote _value_i9) (Litex.denote _value_i10)) = (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i9) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i10) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) from rfl)))).trans (((Eq.refl (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i9) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i10) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)))).trans ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i9) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i10) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)) from by
                                let _litex_original := _equal_wd_1_1
                                let _litex_formula := _litex_original.val.function
                                have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := rfl
                                have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
                                have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) _litex_original.wd.2
                                exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_original.val.argument) = (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue (Litex.denote _value_i9) (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue (Litex.denote _value_i10) (Litex.SetSemantics.emptyValue (M := M))))) : ℂ)); exact (congrArg₂ (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i9), (Litex.denote _value_i10)]) (M.number (1 : ℂ)) = (Litex.denote _value_i9) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i9), (Litex.denote _value_i10)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i9), (Litex.denote _value_i10)]) (M.number (2 : ℂ)) = (Litex.denote _value_i10) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i9), (Litex.denote _value_i10)] (1 : Fin 2)))))
                              )).symm))))
                            )
                        )
                      exact h_578
                    )
                    apply Litex.functionExtOnDomain (Litex.identityMatrix _value_i1 h_267) (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i4 _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 _raw_i5 h_485 h_490 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_485)
                        have h_485 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_485
                        have h_486 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).1
                              )
                          )
                        have h_487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.1
                              )
                          )
                        have h_488 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.2
                              )
                          )
                        have h_489 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_485)
                              )
                          )
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_490)
                        have h_490 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_490
                        have h_491 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).1
                              )
                          )
                        have h_492 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.1
                              )
                          )
                        have h_493 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.2
                              )
                          )
                        have h_494 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_490)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_matrix := (Litex.identityMatrix _value_i1 h_267); let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)) (Litex.inOfSame (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i4 _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 _raw_i5 h_485 h_490 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_485)
                        have h_485 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_485
                        have h_486 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).1
                              )
                          )
                        have h_487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.1
                              )
                          )
                        have h_488 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.2
                              )
                          )
                        have h_489 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_485)
                              )
                          )
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_490)
                        have h_490 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_490
                        have h_491 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).1
                              )
                          )
                        have h_492 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.1
                              )
                          )
                        have h_493 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.2
                              )
                          )
                        have h_494 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_490)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i4 _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 _raw_i5 h_485 h_490 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_485)
                        have h_485 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_485
                        have h_486 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).1
                              )
                          )
                        have h_487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.1
                              )
                          )
                        have h_488 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.2
                              )
                          )
                        have h_489 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_485)
                              )
                          )
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_490)
                        have h_490 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_490
                        have h_491 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).1
                              )
                          )
                        have h_492 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.1
                              )
                          )
                        have h_493 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.2
                              )
                          )
                        have h_494 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_490)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i4 _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 _raw_i5 h_485 h_490 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_485)
                        have h_485 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_485
                        have h_486 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).1
                              )
                          )
                        have h_487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.1
                              )
                          )
                        have h_488 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.2
                              )
                          )
                        have h_489 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_485)
                              )
                          )
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_490)
                        have h_490 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_490
                        have h_491 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).1
                              )
                          )
                        have h_492 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.1
                              )
                          )
                        have h_493 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.2
                              )
                          )
                        have h_494 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_490)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)))) (by rfl)
                    intro _preimage_input _preimage_domain
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                      have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                      have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))
                    have _repack : _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) := (by
                      apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                      apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                      funext i
                      fin_cases i <;> norm_num [Litex.FiniteFunction.index])
                    exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.identityMatrix _value_i1 h_267)) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i4 _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 _raw_i5 h_485 h_490 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_485)
                        have h_485 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_485
                        have h_486 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).1
                              )
                          )
                        have h_487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.1
                              )
                          )
                        have h_488 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.2
                              )
                          )
                        have h_489 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_485)
                              )
                          )
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_490)
                        have h_490 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_490
                        have h_491 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).1
                              )
                          )
                        have h_492 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.1
                              )
                          )
                        have h_493 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.2
                              )
                          )
                        have h_494 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_490)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          let _wd_2_1 := (let _setElement_0 := _value_i5;
                            let _setTail_1 := Litex.emptySet (M := M);
                            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                            _setTail_0);
                          (Litex.intersect _wd_2_0 _wd_2_1));
                          (Litex.finiteSetSize _wd_1_0 (by
                            let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            let _wd_2_1 := (let _setElement_0 := _value_i5;
                              let _setTail_1 := Litex.emptySet (M := M);
                              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                              _setTail_0);
                            (Litex.intersect _wd_2_0 _wd_2_1))
                            exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0)) (by
                              let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                                let _setTail_1 := Litex.emptySet (M := M);
                                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                _setTail_0)
                              exact (let _finite_tail_0 := _atomic_wd_3_0;
                              let _finite_tail_1 := _finite_tail_0.val.tail;
                              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                              _finite_0))))))
                          exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                      exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))) x) _repack) (_pointwise (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))
                  )
                )
            )
          exact (let _equal_wd_1_0 := (Litex.identityMatrix _value_i1 h_267);
          let _equal_wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i2 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i3 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
            have _litex_checked_return : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i3 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i2 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i3 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i2 _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i2 _raw_i3 h_1621 h_1626 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1621)
              have h_1621 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_1621
              have h_1622 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i2 h_1621).1
                    )
                )
              have h_1623 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i2 h_1621).2.1
                    )
                )
              have h_1624 : Litex.Le _value_i2 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i2 h_1621).2.2
                    )
                )
              have h_1625 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1621)
                    )
                )
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1626)
              have h_1626 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_1626
              have h_1627 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i3 h_1626).1
                    )
                )
              have h_1628 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i3 h_1626).2.1
                    )
                )
              have h_1629 : Litex.Le _value_i3 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i3 h_1626).2.2
                    )
                )
              have h_1630 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1626)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
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
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
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
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i2;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i3;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))))
                exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
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
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i2;
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
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i2;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i3;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))))
                exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
            exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_269).trans (by
            let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
            have _litex_checked_return : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (M := M) (Litex.SetSemantics.insertValue _raw_i4 (Litex.SetSemantics.emptyValue (M := M))) (fun _intersection_element : M.Value => M.mem _intersection_element (Litex.SetSemantics.insertValue _raw_i5 (Litex.SetSemantics.emptyValue (M := M))))) : ℂ))) _raw_i4 _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i4 _raw_i5 h_485 h_490 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_485)
              have h_485 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_485
              have h_486 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).1
                    )
                )
              have h_487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.1
                    )
                )
              have h_488 : Litex.Le _value_i4 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 h_485).2.2
                    )
                )
              have h_489 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_485)
                    )
                )
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_490)
              have h_490 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) := h_490
              have h_491 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).1
                    )
                )
              have h_492 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.1
                    )
                )
              have h_493 : Litex.Le _value_i5 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 h_490).2.2
                    )
                )
              have h_494 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_490)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_2_1 := (let _setElement_0 := _value_i5;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_2_0 _wd_2_1));
                (Litex.finiteSetSize _wd_1_0 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_2_1 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_2_0 _wd_2_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))))
                exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                let _wd_2_1 := (let _setElement_0 := _value_i5;
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0);
                (Litex.intersect _wd_2_0 _wd_2_1));
                (Litex.finiteSetSize _wd_1_0 (by
                  let _atomic_wd_2_0 := (let _wd_2_0 := (let _setElement_0 := _value_i4;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_2_1 := (let _setElement_0 := _value_i5;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.intersect _wd_2_0 _wd_2_1))
                  exact (Litex.finiteSetIntersect _atomic_wd_2_0 (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i4;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0)) (by
                    let _atomic_wd_3_0 := (let _setElement_0 := _value_i5;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (let _finite_tail_0 := _atomic_wd_3_0;
                    let _finite_tail_1 := _finite_tail_0.val.tail;
                    have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
                    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
                    _finite_0))))))
                exact (Litex.naturalToReal _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_267)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
            exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
            let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_1_1
            exact (show Litex.Same _left _right from rfl))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_matrix_x5f_formula_x2f_statement_x2e_lit
