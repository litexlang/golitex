import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_named_x5f_fold_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.Z (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))))
theorem h_57 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_58 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by
  intro _raw_i4 _raw_i5 h_72 h_73 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_72)
  have h_72 : Litex.In _value_i4 (Litex.Z (M := M)) := h_72
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_73)
  have h_73 : Litex.In _value_i5 (Litex.Z (M := M)) := h_73
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_72) (Litex.integerToComplex _value_i5 h_73))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_72) (Litex.integerToComplex _value_i5 h_73))
    exact (Litex.addInZ _value_i4 _value_i5 h_72 h_73))))
theorem h_177 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_178 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_4611 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_1_1 := (_object_i1 (M := M));
  let _wd_1_2 := (_object_i3 (M := M));
  let _wd_1_3 := (Litex.number (M := M) (10 : ℂ));
  (let h_4613 : (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact (let _finite_tail_0 := _atomic_wd_1_0;
    let _finite_tail_1 := _finite_tail_0.val.tail;
    let _finite_tail_2 := _finite_tail_1.val.tail;
    have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
    have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
    _finite_0));
  let h_4615 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
  let h_4624 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_4637 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_4638 : Litex.In _value_i13 (Litex.Z (M := M))), (by
    let _object_w42 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_4637 h_4638 True.intro)
    let _object_w43 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_4637) (Litex.integerToComplex _value_i13 h_4638))
    let _object_w44 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i12 (h_177 (M := M)) h_4638 h_4637 True.intro)
    let _object_w45 := (Litex.add _value_i13 _value_i12 (Litex.integerToComplex _value_i13 h_4638) (Litex.integerToComplex _value_i12 h_4637))
    exact (((by
      let _equal_wd_2_0 := _object_w42
      let _equal_wd_2_1 := _object_w43
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w44
      let _equal_wd_2_1 := _object_w45
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w43
      let _equal_wd_2_1 := _object_w45
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
      let _equal_wd_2_0 := _object_w42
      let _equal_wd_2_1 := _object_w44
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))
  ) := (by
    intro _Host_i12 _rep_i12 _value_i12 h_4637 _Host_i13 _rep_i13 _value_i13 h_4638
    let _object_w42 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_4637 h_4638 True.intro)
    let _object_w43 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_4637) (Litex.integerToComplex _value_i13 h_4638))
    have h_4620 : (by
      let _equal_wd_2_0 := _object_w42
      let _equal_wd_2_1 := _object_w43
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_2_0 := _object_w42;
            let _equal_wd_2_1 := _object_w43;
            (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
              let _litex_original := _equal_wd_2_0
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i12;
              let _wd_2_2 := _value_i13;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_4637 h_4638 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w44 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i12 (h_177 (M := M)) h_4638 h_4637 True.intro)
    let _object_w45 := (Litex.add _value_i13 _value_i12 (Litex.integerToComplex _value_i13 h_4638) (Litex.integerToComplex _value_i12 h_4637))
    have h_4621 : (by
      let _equal_wd_2_0 := _object_w44
      let _equal_wd_2_1 := _object_w45
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_2_0 := _object_w44;
            let _equal_wd_2_1 := _object_w45;
            (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i12)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i12)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) from by
              let _litex_original := _equal_wd_2_0
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i13;
              let _wd_2_2 := _value_i12;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_4638 h_4637 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) from rfl))
            ))).trans _litex_residual)))
          )
      )
    have h_4622 : (by
      let _equal_wd_2_0 := _object_w43
      let _equal_wd_2_1 := _object_w45
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_4637)) + (Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_4638))) ((Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_4638)) + (Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_4637))) (Litex.NativeBridge.denoteAdd _value_i12 _value_i13 (_object_w43).wd.1 (_object_w43).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_4637)) (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_4638))) (Litex.NativeBridge.denoteAdd _value_i13 _value_i12 (_object_w45).wd.1 (_object_w45).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_4638)) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_4637))) (by ring!))
          )
      )
    have h_4623 : (by
      let _equal_wd_2_0 := _object_w42
      let _equal_wd_2_1 := _object_w44
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            ((((h_4620).trans h_4622)).trans (h_4621).symm)
          )
      )
    exact (And.intro h_4620 (And.intro h_4621 (And.intro h_4622 h_4623)))
  );
  let h_5152 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_5165 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_5166 : Litex.In _value_i13 (Litex.Z (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_5167 : Litex.In _value_i14 (Litex.Z (M := M))), (by
    let _object_w47 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_5165 h_5166 True.intro)
    let _object_w48 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))
    let _object_w49 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i14 (h_177 (M := M)) h_5166 h_5167 True.intro)
    let _object_w50 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167))
    let _object_w51 := (let _wd_2_0 := _object_w47;
    let _wd_2_1 := _value_i14;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
      let _atomic_wd_1_0 := _object_w47
      exact (by
        let _litex_return_call := _object_w47
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_5167 True.intro))
    let _object_w52 := (let _wd_2_0 := _object_w48;
    let _wd_2_1 := _value_i14;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
      let _atomic_wd_1_0 := _object_w48
      exact (Litex.addInZ _value_i12 _value_i13 h_5165 h_5166)) h_5167 True.intro))
    let _object_w53 := (let _wd_2_0 := _object_w48;
    let _wd_2_1 := _value_i14;
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _object_w48
      exact (Litex.addInC _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))) (Litex.integerToComplex _wd_2_1 h_5167)))
    let _object_w54 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w49;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
      let _atomic_wd_1_0 := _object_w49
      exact (by
        let _litex_return_call := _object_w49
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    let _object_w55 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w50;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
      let _atomic_wd_1_0 := _object_w50
      exact (Litex.addInZ _value_i13 _value_i14 h_5166 h_5167)) True.intro))
    let _object_w56 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w50;
    (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_5165) (by
      let _atomic_wd_1_0 := _object_w50
      exact (Litex.addInC _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167)))))
    exact (((by
      let _equal_wd_2_0 := _object_w47
      let _equal_wd_2_1 := _object_w48
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w49
      let _equal_wd_2_1 := _object_w50
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w51
      let _equal_wd_2_1 := _object_w52
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w52
      let _equal_wd_2_1 := _object_w53
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w54
      let _equal_wd_2_1 := _object_w55
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w55
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w53
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
      let _equal_wd_2_0 := _object_w51
      let _equal_wd_2_1 := _object_w54
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))))))))))
  ) := (by
    intro _Host_i12 _rep_i12 _value_i12 h_5165 _Host_i13 _rep_i13 _value_i13 h_5166 _Host_i14 _rep_i14 _value_i14 h_5167
    let _object_w47 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_5165 h_5166 True.intro)
    let _object_w48 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))
    have h_5144 : (by
      let _equal_wd_2_0 := _object_w47
      let _equal_wd_2_1 := _object_w48
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_2_0 := _object_w47;
            let _equal_wd_2_1 := _object_w48;
            (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
              let _litex_original := _equal_wd_2_0
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i12;
              let _wd_2_2 := _value_i13;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_5165 h_5166 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w49 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i14 (h_177 (M := M)) h_5166 h_5167 True.intro)
    let _object_w50 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167))
    have h_5145 : (by
      let _equal_wd_2_0 := _object_w49
      let _equal_wd_2_1 := _object_w50
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_2_0 := _object_w49;
            let _equal_wd_2_1 := _object_w50;
            (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
              let _litex_original := _equal_wd_2_0
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i13;
              let _wd_2_2 := _value_i14;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_5166 h_5167 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w51 := (let _wd_2_0 := _object_w47;
    let _wd_2_1 := _value_i14;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
      let _atomic_wd_1_0 := _object_w47
      exact (by
        let _litex_return_call := _object_w47
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_5167 True.intro))
    let _object_w52 := (let _wd_2_0 := _object_w48;
    let _wd_2_1 := _value_i14;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
      let _atomic_wd_1_0 := _object_w48
      exact (Litex.addInZ _value_i12 _value_i13 h_5165 h_5166)) h_5167 True.intro))
    have h_5146 : (by
      let _equal_wd_2_0 := _object_w51
      let _equal_wd_2_1 := _object_w52
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_5144 (show @Eq M.Value _ _ from Eq.refl _)))
          )
      )
    let _object_w53 := (let _wd_2_0 := _object_w48;
    let _wd_2_1 := _value_i14;
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _object_w48
      exact (Litex.addInC _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))) (Litex.integerToComplex _wd_2_1 h_5167)))
    have h_5147 : (by
      let _equal_wd_2_0 := _object_w52
      let _equal_wd_2_1 := _object_w53
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)), (Litex.denote _value_i14)])) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) from by
              have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)), (Litex.denote _value_i14)])) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) from by
              let _litex_original := _object_w52
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _object_w48;
              let _wd_2_2 := _value_i14;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
                let _atomic_wd_1_0 := _object_w48
                exact (Litex.addInZ _value_i12 _value_i13 h_5165 h_5166)) h_5167 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w54 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w49;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
      let _atomic_wd_1_0 := _object_w49
      exact (by
        let _litex_return_call := _object_w49
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    let _object_w55 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w50;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
      let _atomic_wd_1_0 := _object_w50
      exact (Litex.addInZ _value_i13 _value_i14 h_5166 h_5167)) True.intro))
    have h_5148 : (by
      let _equal_wd_2_0 := _object_w54
      let _equal_wd_2_1 := _object_w55
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_5145))
          )
      )
    let _object_w56 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w50;
    (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_5165) (by
      let _atomic_wd_1_0 := _object_w50
      exact (Litex.addInC _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167)))))
    have h_5149 : (by
      let _equal_wd_2_0 := _object_w55
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))])) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))])) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) from by
              let _litex_original := _object_w55
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i12;
              let _wd_2_2 := _object_w50;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_5165 (by
                let _atomic_wd_1_0 := _object_w50
                exact (Litex.addInZ _value_i13 _value_i14 h_5166 h_5167)) True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) from rfl))
            ))).trans _litex_residual)
          )
      )
    have h_5150 : (by
      let _equal_wd_2_0 := _object_w53
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_5165)) + (Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_5166))) + (Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_5167))) ((Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_5165)) + ((Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_5166)) + (Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_5167)))) (Litex.NativeBridge.denoteAdd (_object_w53).val.left _value_i14 (_object_w53).wd.1 (_object_w53).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i12 _value_i13 (_object_w48).wd.1 (_object_w48).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_5165)) (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_5166))) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_5167))) (Litex.NativeBridge.denoteAdd _value_i12 (_object_w56).val.right (_object_w56).wd.1 (_object_w56).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_5165)) (Litex.NativeBridge.denoteAdd _value_i13 _value_i14 (_object_w50).wd.1 (_object_w50).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_5166)) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_5167)))) (by ring!))
          )
      )
    have h_5151 : (by
      let _equal_wd_2_0 := _object_w51
      let _equal_wd_2_1 := _object_w54
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            ((((((((h_5146).trans h_5147)).trans h_5150)).trans (h_5149).symm)).trans (h_5148).symm)
          )
      )
    exact (And.intro h_5144 (And.intro h_5145 (And.intro h_5146 (And.intro h_5147 (And.intro h_5148 (And.intro h_5149 (And.intro h_5150 h_5151)))))))
  );
  let h_6801 : (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M)))))));
  Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) h_4613 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) (h_177 (M := M))) h_4615 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => True) i).mpr ⟨h_6801 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_4624 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_5152 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (15 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
          let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_1_1 := (_object_i1 (M := M));
        let _wd_1_2 := (_object_i3 (M := M));
        let _wd_1_3 := (Litex.number (M := M) (10 : ℂ));
        (let h_4613 : (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0));
        let h_4615 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
        let h_4624 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_4637 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_4638 : Litex.In _value_i13 (Litex.Z (M := M))), (by
          let _object_w42 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_4637 h_4638 True.intro)
          let _object_w43 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_4637) (Litex.integerToComplex _value_i13 h_4638))
          let _object_w44 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i12 (h_177 (M := M)) h_4638 h_4637 True.intro)
          let _object_w45 := (Litex.add _value_i13 _value_i12 (Litex.integerToComplex _value_i13 h_4638) (Litex.integerToComplex _value_i12 h_4637))
          exact (((by
            let _equal_wd_2_0 := _object_w42
            let _equal_wd_2_1 := _object_w43
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w44
            let _equal_wd_2_1 := _object_w45
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w43
            let _equal_wd_2_1 := _object_w45
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
            let _equal_wd_2_0 := _object_w42
            let _equal_wd_2_1 := _object_w44
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))
        ) := (by
          intro _Host_i12 _rep_i12 _value_i12 h_4637 _Host_i13 _rep_i13 _value_i13 h_4638
          let _object_w42 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_4637 h_4638 True.intro)
          let _object_w43 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_4637) (Litex.integerToComplex _value_i13 h_4638))
          have h_4620 : (by
            let _equal_wd_2_0 := _object_w42
            let _equal_wd_2_1 := _object_w43
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_2_0 := _object_w42;
                  let _equal_wd_2_1 := _object_w43;
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
                    let _litex_original := _equal_wd_2_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i12;
                    let _wd_2_2 := _value_i13;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_4637 h_4638 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w44 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i12 (h_177 (M := M)) h_4638 h_4637 True.intro)
          let _object_w45 := (Litex.add _value_i13 _value_i12 (Litex.integerToComplex _value_i13 h_4638) (Litex.integerToComplex _value_i12 h_4637))
          have h_4621 : (by
            let _equal_wd_2_0 := _object_w44
            let _equal_wd_2_1 := _object_w45
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_2_0 := _object_w44;
                  let _equal_wd_2_1 := _object_w45;
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i12)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i12)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) from by
                    let _litex_original := _equal_wd_2_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i13;
                    let _wd_2_2 := _value_i12;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_4638 h_4637 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_4622 : (by
            let _equal_wd_2_0 := _object_w43
            let _equal_wd_2_1 := _object_w45
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_4637)) + (Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_4638))) ((Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_4638)) + (Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_4637))) (Litex.NativeBridge.denoteAdd _value_i12 _value_i13 (_object_w43).wd.1 (_object_w43).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_4637)) (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_4638))) (Litex.NativeBridge.denoteAdd _value_i13 _value_i12 (_object_w45).wd.1 (_object_w45).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_4638)) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_4637))) (by ring!))
                )
            )
          have h_4623 : (by
            let _equal_wd_2_0 := _object_w42
            let _equal_wd_2_1 := _object_w44
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_4620).trans h_4622)).trans (h_4621).symm)
                )
            )
          exact (And.intro h_4620 (And.intro h_4621 (And.intro h_4622 h_4623)))
        );
        let h_5152 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_5165 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_5166 : Litex.In _value_i13 (Litex.Z (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_5167 : Litex.In _value_i14 (Litex.Z (M := M))), (by
          let _object_w47 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_5165 h_5166 True.intro)
          let _object_w48 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))
          let _object_w49 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i14 (h_177 (M := M)) h_5166 h_5167 True.intro)
          let _object_w50 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167))
          let _object_w51 := (let _wd_2_0 := _object_w47;
          let _wd_2_1 := _value_i14;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w47
            exact (by
              let _litex_return_call := _object_w47
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_5167 True.intro))
          let _object_w52 := (let _wd_2_0 := _object_w48;
          let _wd_2_1 := _value_i14;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w48
            exact (Litex.addInZ _value_i12 _value_i13 h_5165 h_5166)) h_5167 True.intro))
          let _object_w53 := (let _wd_2_0 := _object_w48;
          let _wd_2_1 := _value_i14;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w48
            exact (Litex.addInC _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))) (Litex.integerToComplex _wd_2_1 h_5167)))
          let _object_w54 := (let _wd_2_0 := _value_i12;
          let _wd_2_1 := _object_w49;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
            let _atomic_wd_1_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
          let _object_w55 := (let _wd_2_0 := _value_i12;
          let _wd_2_1 := _object_w50;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
            let _atomic_wd_1_0 := _object_w50
            exact (Litex.addInZ _value_i13 _value_i14 h_5166 h_5167)) True.intro))
          let _object_w56 := (let _wd_2_0 := _value_i12;
          let _wd_2_1 := _object_w50;
          (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_5165) (by
            let _atomic_wd_1_0 := _object_w50
            exact (Litex.addInC _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167)))))
          exact (((by
            let _equal_wd_2_0 := _object_w47
            let _equal_wd_2_1 := _object_w48
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w49
            let _equal_wd_2_1 := _object_w50
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w51
            let _equal_wd_2_1 := _object_w52
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w52
            let _equal_wd_2_1 := _object_w53
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w54
            let _equal_wd_2_1 := _object_w55
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w55
            let _equal_wd_2_1 := _object_w56
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w53
            let _equal_wd_2_1 := _object_w56
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
            let _equal_wd_2_0 := _object_w51
            let _equal_wd_2_1 := _object_w54
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))))))))))
        ) := (by
          intro _Host_i12 _rep_i12 _value_i12 h_5165 _Host_i13 _rep_i13 _value_i13 h_5166 _Host_i14 _rep_i14 _value_i14 h_5167
          let _object_w47 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_5165 h_5166 True.intro)
          let _object_w48 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))
          have h_5144 : (by
            let _equal_wd_2_0 := _object_w47
            let _equal_wd_2_1 := _object_w48
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_2_0 := _object_w47;
                  let _equal_wd_2_1 := _object_w48;
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
                    let _litex_original := _equal_wd_2_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i12;
                    let _wd_2_2 := _value_i13;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_5165 h_5166 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w49 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i14 (h_177 (M := M)) h_5166 h_5167 True.intro)
          let _object_w50 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167))
          have h_5145 : (by
            let _equal_wd_2_0 := _object_w49
            let _equal_wd_2_1 := _object_w50
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_2_0 := _object_w49;
                  let _equal_wd_2_1 := _object_w50;
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
                    let _litex_original := _equal_wd_2_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i13;
                    let _wd_2_2 := _value_i14;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_5166 h_5167 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w51 := (let _wd_2_0 := _object_w47;
          let _wd_2_1 := _value_i14;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w47
            exact (by
              let _litex_return_call := _object_w47
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_5167 True.intro))
          let _object_w52 := (let _wd_2_0 := _object_w48;
          let _wd_2_1 := _value_i14;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w48
            exact (Litex.addInZ _value_i12 _value_i13 h_5165 h_5166)) h_5167 True.intro))
          have h_5146 : (by
            let _equal_wd_2_0 := _object_w51
            let _equal_wd_2_1 := _object_w52
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_5144 (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w53 := (let _wd_2_0 := _object_w48;
          let _wd_2_1 := _value_i14;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w48
            exact (Litex.addInC _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))) (Litex.integerToComplex _wd_2_1 h_5167)))
          have h_5147 : (by
            let _equal_wd_2_0 := _object_w52
            let _equal_wd_2_1 := _object_w53
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)), (Litex.denote _value_i14)])) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) from by
                    have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)), (Litex.denote _value_i14)])) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) from by
                    let _litex_original := _object_w52
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _object_w48;
                    let _wd_2_2 := _value_i14;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
                      let _atomic_wd_1_0 := _object_w48
                      exact (Litex.addInZ _value_i12 _value_i13 h_5165 h_5166)) h_5167 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w54 := (let _wd_2_0 := _value_i12;
          let _wd_2_1 := _object_w49;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
            let _atomic_wd_1_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
          let _object_w55 := (let _wd_2_0 := _value_i12;
          let _wd_2_1 := _object_w50;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
            let _atomic_wd_1_0 := _object_w50
            exact (Litex.addInZ _value_i13 _value_i14 h_5166 h_5167)) True.intro))
          have h_5148 : (by
            let _equal_wd_2_0 := _object_w54
            let _equal_wd_2_1 := _object_w55
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_5145))
                )
            )
          let _object_w56 := (let _wd_2_0 := _value_i12;
          let _wd_2_1 := _object_w50;
          (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_5165) (by
            let _atomic_wd_1_0 := _object_w50
            exact (Litex.addInC _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167)))))
          have h_5149 : (by
            let _equal_wd_2_0 := _object_w55
            let _equal_wd_2_1 := _object_w56
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))])) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))])) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) from by
                    let _litex_original := _object_w55
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i12;
                    let _wd_2_2 := _object_w50;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_5165 (by
                      let _atomic_wd_1_0 := _object_w50
                      exact (Litex.addInZ _value_i13 _value_i14 h_5166 h_5167)) True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_5150 : (by
            let _equal_wd_2_0 := _object_w53
            let _equal_wd_2_1 := _object_w56
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_5165)) + (Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_5166))) + (Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_5167))) ((Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_5165)) + ((Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_5166)) + (Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_5167)))) (Litex.NativeBridge.denoteAdd (_object_w53).val.left _value_i14 (_object_w53).wd.1 (_object_w53).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i12 _value_i13 (_object_w48).wd.1 (_object_w48).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_5165)) (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_5166))) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_5167))) (Litex.NativeBridge.denoteAdd _value_i12 (_object_w56).val.right (_object_w56).wd.1 (_object_w56).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_5165)) (Litex.NativeBridge.denoteAdd _value_i13 _value_i14 (_object_w50).wd.1 (_object_w50).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_5166)) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_5167)))) (by ring!))
                )
            )
          have h_5151 : (by
            let _equal_wd_2_0 := _object_w51
            let _equal_wd_2_1 := _object_w54
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((((((h_5146).trans h_5147)).trans h_5150)).trans (h_5149).symm)).trans (h_5148).symm)
                )
            )
          exact (And.intro h_5144 (And.intro h_5145 (And.intro h_5146 (And.intro h_5147 (And.intro h_5148 (And.intro h_5149 (And.intro h_5150 h_5151)))))))
        );
        let h_6801 : (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M)))))));
        Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) h_4613 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) (h_177 (M := M))) h_4615 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => True) i).mpr ⟨h_6801 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_4624 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_5152 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (15 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (15 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
          let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_1_1 := (_object_i1 (M := M));
        let _wd_1_2 := (_object_i3 (M := M));
        let _wd_1_3 := (Litex.number (M := M) (10 : ℂ));
        (let h_180 : (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0));
        let h_182 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
        let h_191 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_204 : Litex.In _value_i6 (Litex.Z (M := M))) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_205 : Litex.In _value_i7 (Litex.Z (M := M))), (by
          let _object_w10 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_204 h_205 True.intro)
          let _object_w11 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_204) (Litex.integerToComplex _value_i7 h_205))
          let _object_w12 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i6 (h_177 (M := M)) h_205 h_204 True.intro)
          let _object_w13 := (Litex.add _value_i7 _value_i6 (Litex.integerToComplex _value_i7 h_205) (Litex.integerToComplex _value_i6 h_204))
          exact (((by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
        ) := (by
          intro _Host_i6 _rep_i6 _value_i6 h_204 _Host_i7 _rep_i7 _value_i7 h_205
          let _object_w10 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_204 h_205 True.intro)
          let _object_w11 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_204) (Litex.integerToComplex _value_i7 h_205))
          have h_187 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  let _equal_wd_1_1 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i6;
                    let _wd_2_2 := _value_i7;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_204 h_205 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w12 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i6 (h_177 (M := M)) h_205 h_204 True.intro)
          let _object_w13 := (Litex.add _value_i7 _value_i6 (Litex.integerToComplex _value_i7 h_205) (Litex.integerToComplex _value_i6 h_204))
          have h_188 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w12;
                  let _equal_wd_1_1 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i7;
                    let _wd_2_2 := _value_i6;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_205 h_204 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_189 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_204)) + (Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_205))) ((Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_205)) + (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_204))) (Litex.NativeBridge.denoteAdd _value_i6 _value_i7 (_object_w11).wd.1 (_object_w11).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_204)) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_205))) (Litex.NativeBridge.denoteAdd _value_i7 _value_i6 (_object_w13).wd.1 (_object_w13).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_205)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_204))) (by ring!))
                )
            )
          have h_190 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_187).trans h_189)).trans (h_188).symm)
                )
            )
          exact (And.intro h_187 (And.intro h_188 (And.intro h_189 h_190)))
        );
        let h_719 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_732 : Litex.In _value_i6 (Litex.Z (M := M))) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_733 : Litex.In _value_i7 (Litex.Z (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_734 : Litex.In _value_i8 (Litex.Z (M := M))), (by
          let _object_w15 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_732 h_733 True.intro)
          let _object_w16 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))
          let _object_w17 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i8 (h_177 (M := M)) h_733 h_734 True.intro)
          let _object_w18 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734))
          let _object_w19 := (let _wd_2_0 := _object_w15;
          let _wd_2_1 := _value_i8;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w15
            exact (by
              let _litex_return_call := _object_w15
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_734 True.intro))
          let _object_w20 := (let _wd_2_0 := _object_w16;
          let _wd_2_1 := _value_i8;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w16
            exact (Litex.addInZ _value_i6 _value_i7 h_732 h_733)) h_734 True.intro))
          let _object_w21 := (let _wd_2_0 := _object_w16;
          let _wd_2_1 := _value_i8;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w16
            exact (Litex.addInC _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))) (Litex.integerToComplex _wd_2_1 h_734)))
          let _object_w22 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w17;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
            let _atomic_wd_1_0 := _object_w17
            exact (by
              let _litex_return_call := _object_w17
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
          let _object_w23 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w18;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
            let _atomic_wd_1_0 := _object_w18
            exact (Litex.addInZ _value_i7 _value_i8 h_733 h_734)) True.intro))
          let _object_w24 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w18;
          (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_732) (by
            let _atomic_wd_1_0 := _object_w18
            exact (Litex.addInC _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734)))))
          exact (((by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w20
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w20
            let _equal_wd_1_1 := _object_w21
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w22
            let _equal_wd_1_1 := _object_w23
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w23
            let _equal_wd_1_1 := _object_w24
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w21
            let _equal_wd_1_1 := _object_w24
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w22
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
        ) := (by
          intro _Host_i6 _rep_i6 _value_i6 h_732 _Host_i7 _rep_i7 _value_i7 h_733 _Host_i8 _rep_i8 _value_i8 h_734
          let _object_w15 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_732 h_733 True.intro)
          let _object_w16 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))
          have h_711 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w15;
                  let _equal_wd_1_1 := _object_w16;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i6;
                    let _wd_2_2 := _value_i7;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_732 h_733 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w17 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i8 (h_177 (M := M)) h_733 h_734 True.intro)
          let _object_w18 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734))
          have h_712 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w17;
                  let _equal_wd_1_1 := _object_w18;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i7;
                    let _wd_2_2 := _value_i8;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_733 h_734 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w19 := (let _wd_2_0 := _object_w15;
          let _wd_2_1 := _value_i8;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w15
            exact (by
              let _litex_return_call := _object_w15
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_734 True.intro))
          let _object_w20 := (let _wd_2_0 := _object_w16;
          let _wd_2_1 := _value_i8;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w16
            exact (Litex.addInZ _value_i6 _value_i7 h_732 h_733)) h_734 True.intro))
          have h_713 : (by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w20
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_711 (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w21 := (let _wd_2_0 := _object_w16;
          let _wd_2_1 := _value_i8;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w16
            exact (Litex.addInC _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))) (Litex.integerToComplex _wd_2_1 h_734)))
          have h_714 : (by
            let _equal_wd_1_0 := _object_w20
            let _equal_wd_1_1 := _object_w21
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from by
                    have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from by
                    let _litex_original := _object_w20
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _object_w16;
                    let _wd_2_2 := _value_i8;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
                      let _atomic_wd_1_0 := _object_w16
                      exact (Litex.addInZ _value_i6 _value_i7 h_732 h_733)) h_734 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w22 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w17;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
            let _atomic_wd_1_0 := _object_w17
            exact (by
              let _litex_return_call := _object_w17
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
          let _object_w23 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w18;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
            let _atomic_wd_1_0 := _object_w18
            exact (Litex.addInZ _value_i7 _value_i8 h_733 h_734)) True.intro))
          have h_715 : (by
            let _equal_wd_1_0 := _object_w22
            let _equal_wd_1_1 := _object_w23
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_712))
                )
            )
          let _object_w24 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w18;
          (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_732) (by
            let _atomic_wd_1_0 := _object_w18
            exact (Litex.addInC _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734)))))
          have h_716 : (by
            let _equal_wd_1_0 := _object_w23
            let _equal_wd_1_1 := _object_w24
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))])) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))])) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from by
                    let _litex_original := _object_w23
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i6;
                    let _wd_2_2 := _object_w18;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_732 (by
                      let _atomic_wd_1_0 := _object_w18
                      exact (Litex.addInZ _value_i7 _value_i8 h_733 h_734)) True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_717 : (by
            let _equal_wd_1_0 := _object_w21
            let _equal_wd_1_1 := _object_w24
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_732)) + (Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_733))) + (Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_734))) ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_732)) + ((Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_733)) + (Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_734)))) (Litex.NativeBridge.denoteAdd (_object_w21).val.left _value_i8 (_object_w21).wd.1 (_object_w21).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i6 _value_i7 (_object_w16).wd.1 (_object_w16).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_732)) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_733))) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_734))) (Litex.NativeBridge.denoteAdd _value_i6 (_object_w24).val.right (_object_w24).wd.1 (_object_w24).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_732)) (Litex.NativeBridge.denoteAdd _value_i7 _value_i8 (_object_w18).wd.1 (_object_w18).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_733)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_734)))) (by ring!))
                )
            )
          have h_718 : (by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w22
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((((((h_713).trans h_714)).trans h_717)).trans (h_716).symm)).trans (h_715).symm)
                )
            )
          exact (And.intro h_711 (And.intro h_712 (And.intro h_713 (And.intro h_714 (And.intro h_715 (And.intro h_716 (And.intro h_717 h_718)))))))
        );
        let h_2368 : (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M)))))));
        Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) h_180 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) (h_177 (M := M))) h_182 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => True) i).mpr ⟨h_2368 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_191 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_719 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))))).trans (show (Litex.denote (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
          let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_1_1 := (_object_i1 (M := M));
        let _wd_1_2 := (_object_i3 (M := M));
        let _wd_1_3 := (Litex.number (M := M) (10 : ℂ));
        (let h_180 : (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0));
        let h_182 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
        let h_191 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_204 : Litex.In _value_i6 (Litex.Z (M := M))) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_205 : Litex.In _value_i7 (Litex.Z (M := M))), (by
          let _object_w10 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_204 h_205 True.intro)
          let _object_w11 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_204) (Litex.integerToComplex _value_i7 h_205))
          let _object_w12 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i6 (h_177 (M := M)) h_205 h_204 True.intro)
          let _object_w13 := (Litex.add _value_i7 _value_i6 (Litex.integerToComplex _value_i7 h_205) (Litex.integerToComplex _value_i6 h_204))
          exact (((by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
        ) := (by
          intro _Host_i6 _rep_i6 _value_i6 h_204 _Host_i7 _rep_i7 _value_i7 h_205
          let _object_w10 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_204 h_205 True.intro)
          let _object_w11 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_204) (Litex.integerToComplex _value_i7 h_205))
          have h_187 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  let _equal_wd_1_1 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i6;
                    let _wd_2_2 := _value_i7;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_204 h_205 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w12 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i6 (h_177 (M := M)) h_205 h_204 True.intro)
          let _object_w13 := (Litex.add _value_i7 _value_i6 (Litex.integerToComplex _value_i7 h_205) (Litex.integerToComplex _value_i6 h_204))
          have h_188 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w12;
                  let _equal_wd_1_1 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i7;
                    let _wd_2_2 := _value_i6;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_205 h_204 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_189 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_204)) + (Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_205))) ((Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_205)) + (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_204))) (Litex.NativeBridge.denoteAdd _value_i6 _value_i7 (_object_w11).wd.1 (_object_w11).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_204)) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_205))) (Litex.NativeBridge.denoteAdd _value_i7 _value_i6 (_object_w13).wd.1 (_object_w13).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_205)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_204))) (by ring!))
                )
            )
          have h_190 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_187).trans h_189)).trans (h_188).symm)
                )
            )
          exact (And.intro h_187 (And.intro h_188 (And.intro h_189 h_190)))
        );
        let h_719 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_732 : Litex.In _value_i6 (Litex.Z (M := M))) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_733 : Litex.In _value_i7 (Litex.Z (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_734 : Litex.In _value_i8 (Litex.Z (M := M))), (by
          let _object_w15 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_732 h_733 True.intro)
          let _object_w16 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))
          let _object_w17 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i8 (h_177 (M := M)) h_733 h_734 True.intro)
          let _object_w18 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734))
          let _object_w19 := (let _wd_2_0 := _object_w15;
          let _wd_2_1 := _value_i8;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w15
            exact (by
              let _litex_return_call := _object_w15
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_734 True.intro))
          let _object_w20 := (let _wd_2_0 := _object_w16;
          let _wd_2_1 := _value_i8;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w16
            exact (Litex.addInZ _value_i6 _value_i7 h_732 h_733)) h_734 True.intro))
          let _object_w21 := (let _wd_2_0 := _object_w16;
          let _wd_2_1 := _value_i8;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w16
            exact (Litex.addInC _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))) (Litex.integerToComplex _wd_2_1 h_734)))
          let _object_w22 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w17;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
            let _atomic_wd_1_0 := _object_w17
            exact (by
              let _litex_return_call := _object_w17
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
          let _object_w23 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w18;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
            let _atomic_wd_1_0 := _object_w18
            exact (Litex.addInZ _value_i7 _value_i8 h_733 h_734)) True.intro))
          let _object_w24 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w18;
          (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_732) (by
            let _atomic_wd_1_0 := _object_w18
            exact (Litex.addInC _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734)))))
          exact (((by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w20
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w20
            let _equal_wd_1_1 := _object_w21
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w22
            let _equal_wd_1_1 := _object_w23
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w23
            let _equal_wd_1_1 := _object_w24
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w21
            let _equal_wd_1_1 := _object_w24
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w22
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
        ) := (by
          intro _Host_i6 _rep_i6 _value_i6 h_732 _Host_i7 _rep_i7 _value_i7 h_733 _Host_i8 _rep_i8 _value_i8 h_734
          let _object_w15 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_732 h_733 True.intro)
          let _object_w16 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))
          have h_711 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w15;
                  let _equal_wd_1_1 := _object_w16;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i6;
                    let _wd_2_2 := _value_i7;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_732 h_733 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w17 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i8 (h_177 (M := M)) h_733 h_734 True.intro)
          let _object_w18 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734))
          have h_712 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w17;
                  let _equal_wd_1_1 := _object_w18;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i7;
                    let _wd_2_2 := _value_i8;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_733 h_734 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w19 := (let _wd_2_0 := _object_w15;
          let _wd_2_1 := _value_i8;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w15
            exact (by
              let _litex_return_call := _object_w15
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_734 True.intro))
          let _object_w20 := (let _wd_2_0 := _object_w16;
          let _wd_2_1 := _value_i8;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
            let _atomic_wd_1_0 := _object_w16
            exact (Litex.addInZ _value_i6 _value_i7 h_732 h_733)) h_734 True.intro))
          have h_713 : (by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w20
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_711 (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w21 := (let _wd_2_0 := _object_w16;
          let _wd_2_1 := _value_i8;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w16
            exact (Litex.addInC _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))) (Litex.integerToComplex _wd_2_1 h_734)))
          have h_714 : (by
            let _equal_wd_1_0 := _object_w20
            let _equal_wd_1_1 := _object_w21
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from by
                    have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from by
                    let _litex_original := _object_w20
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _object_w16;
                    let _wd_2_2 := _value_i8;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
                      let _atomic_wd_1_0 := _object_w16
                      exact (Litex.addInZ _value_i6 _value_i7 h_732 h_733)) h_734 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w22 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w17;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
            let _atomic_wd_1_0 := _object_w17
            exact (by
              let _litex_return_call := _object_w17
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
          let _object_w23 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w18;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
            let _atomic_wd_1_0 := _object_w18
            exact (Litex.addInZ _value_i7 _value_i8 h_733 h_734)) True.intro))
          have h_715 : (by
            let _equal_wd_1_0 := _object_w22
            let _equal_wd_1_1 := _object_w23
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_712))
                )
            )
          let _object_w24 := (let _wd_2_0 := _value_i6;
          let _wd_2_1 := _object_w18;
          (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_732) (by
            let _atomic_wd_1_0 := _object_w18
            exact (Litex.addInC _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734)))))
          have h_716 : (by
            let _equal_wd_1_0 := _object_w23
            let _equal_wd_1_1 := _object_w24
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))])) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))])) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from by
                    let _litex_original := _object_w23
                    let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                    let _wd_2_1 := _value_i6;
                    let _wd_2_2 := _object_w18;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_732 (by
                      let _atomic_wd_1_0 := _object_w18
                      exact (Litex.addInZ _value_i7 _value_i8 h_733 h_734)) True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_717 : (by
            let _equal_wd_1_0 := _object_w21
            let _equal_wd_1_1 := _object_w24
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_732)) + (Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_733))) + (Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_734))) ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_732)) + ((Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_733)) + (Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_734)))) (Litex.NativeBridge.denoteAdd (_object_w21).val.left _value_i8 (_object_w21).wd.1 (_object_w21).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i6 _value_i7 (_object_w16).wd.1 (_object_w16).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_732)) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_733))) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_734))) (Litex.NativeBridge.denoteAdd _value_i6 (_object_w24).val.right (_object_w24).wd.1 (_object_w24).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_732)) (Litex.NativeBridge.denoteAdd _value_i7 _value_i8 (_object_w18).wd.1 (_object_w18).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_733)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_734)))) (by ring!))
                )
            )
          have h_718 : (by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w22
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((((((h_713).trans h_714)).trans h_717)).trans (h_716).symm)).trans (h_715).symm)
                )
            )
          exact (And.intro h_711 (And.intro h_712 (And.intro h_713 (And.intro h_714 (And.intro h_715 (And.intro h_716 (And.intro h_717 h_718)))))))
        );
        let h_2368 : (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M)))))));
        Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) h_180 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) (h_177 (M := M))) h_182 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => True) i).mpr ⟨h_2368 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_191 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_719 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))) = M.number (15 : ℂ) from (by
          let _fold := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_1_1 := (_object_i1 (M := M));
          let _wd_1_2 := (_object_i3 (M := M));
          let _wd_1_3 := (Litex.number (M := M) (10 : ℂ));
          (let h_180 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            let _finite_tail_2 := _finite_tail_1.val.tail;
            have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
            have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0));
          let h_182 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
          let h_191 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_204 : Litex.In _value_i6 (Litex.Z (M := M))) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_205 : Litex.In _value_i7 (Litex.Z (M := M))), (by
            let _object_w10 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_204 h_205 True.intro)
            let _object_w11 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_204) (Litex.integerToComplex _value_i7 h_205))
            let _object_w12 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i6 (h_177 (M := M)) h_205 h_204 True.intro)
            let _object_w13 := (Litex.add _value_i7 _value_i6 (Litex.integerToComplex _value_i7 h_205) (Litex.integerToComplex _value_i6 h_204))
            exact (((by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w11
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w12
              let _equal_wd_1_1 := _object_w13
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w11
              let _equal_wd_1_1 := _object_w13
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w12
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
          ) := (by
            intro _Host_i6 _rep_i6 _value_i6 h_204 _Host_i7 _rep_i7 _value_i7 h_205
            let _object_w10 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_204 h_205 True.intro)
            let _object_w11 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_204) (Litex.integerToComplex _value_i7 h_205))
            have h_187 : (by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w11
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w10;
                    let _equal_wd_1_1 := _object_w11;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                      let _wd_2_1 := _value_i6;
                      let _wd_2_2 := _value_i7;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_204 h_205 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from rfl))
                    ))).trans _litex_residual)))
                  )
              )
            let _object_w12 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i6 (h_177 (M := M)) h_205 h_204 True.intro)
            let _object_w13 := (Litex.add _value_i7 _value_i6 (Litex.integerToComplex _value_i7 h_205) (Litex.integerToComplex _value_i6 h_204))
            have h_188 : (by
              let _equal_wd_1_0 := _object_w12
              let _equal_wd_1_1 := _object_w13
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w12;
                    let _equal_wd_1_1 := _object_w13;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                      let _wd_2_1 := _value_i7;
                      let _wd_2_2 := _value_i6;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_205 h_204 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i6)) from rfl))
                    ))).trans _litex_residual)))
                  )
              )
            have h_189 : (by
              let _equal_wd_1_0 := _object_w11
              let _equal_wd_1_1 := _object_w13
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_204)) + (Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_205))) ((Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_205)) + (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_204))) (Litex.NativeBridge.denoteAdd _value_i6 _value_i7 (_object_w11).wd.1 (_object_w11).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_204)) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_205))) (Litex.NativeBridge.denoteAdd _value_i7 _value_i6 (_object_w13).wd.1 (_object_w13).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_205)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_204))) (by ring!))
                  )
              )
            have h_190 : (by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w12
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    ((((h_187).trans h_189)).trans (h_188).symm)
                  )
              )
            exact (And.intro h_187 (And.intro h_188 (And.intro h_189 h_190)))
          );
          let h_719 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_732 : Litex.In _value_i6 (Litex.Z (M := M))) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_733 : Litex.In _value_i7 (Litex.Z (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_734 : Litex.In _value_i8 (Litex.Z (M := M))), (by
            let _object_w15 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_732 h_733 True.intro)
            let _object_w16 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))
            let _object_w17 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i8 (h_177 (M := M)) h_733 h_734 True.intro)
            let _object_w18 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734))
            let _object_w19 := (let _wd_2_0 := _object_w15;
            let _wd_2_1 := _value_i8;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
              let _atomic_wd_1_0 := _object_w15
              exact (by
                let _litex_return_call := _object_w15
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_734 True.intro))
            let _object_w20 := (let _wd_2_0 := _object_w16;
            let _wd_2_1 := _value_i8;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
              let _atomic_wd_1_0 := _object_w16
              exact (Litex.addInZ _value_i6 _value_i7 h_732 h_733)) h_734 True.intro))
            let _object_w21 := (let _wd_2_0 := _object_w16;
            let _wd_2_1 := _value_i8;
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w16
              exact (Litex.addInC _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))) (Litex.integerToComplex _wd_2_1 h_734)))
            let _object_w22 := (let _wd_2_0 := _value_i6;
            let _wd_2_1 := _object_w17;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
              let _atomic_wd_1_0 := _object_w17
              exact (by
                let _litex_return_call := _object_w17
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            let _object_w23 := (let _wd_2_0 := _value_i6;
            let _wd_2_1 := _object_w18;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
              let _atomic_wd_1_0 := _object_w18
              exact (Litex.addInZ _value_i7 _value_i8 h_733 h_734)) True.intro))
            let _object_w24 := (let _wd_2_0 := _value_i6;
            let _wd_2_1 := _object_w18;
            (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_732) (by
              let _atomic_wd_1_0 := _object_w18
              exact (Litex.addInC _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734)))))
            exact (((by
              let _equal_wd_1_0 := _object_w15
              let _equal_wd_1_1 := _object_w16
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w17
              let _equal_wd_1_1 := _object_w18
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w19
              let _equal_wd_1_1 := _object_w20
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w20
              let _equal_wd_1_1 := _object_w21
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w22
              let _equal_wd_1_1 := _object_w23
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w23
              let _equal_wd_1_1 := _object_w24
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w21
              let _equal_wd_1_1 := _object_w24
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _object_w19
              let _equal_wd_1_1 := _object_w22
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
          ) := (by
            intro _Host_i6 _rep_i6 _value_i6 h_732 _Host_i7 _rep_i7 _value_i7 h_733 _Host_i8 _rep_i8 _value_i8 h_734
            let _object_w15 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i6 _value_i7 (h_177 (M := M)) h_732 h_733 True.intro)
            let _object_w16 := (Litex.add _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))
            have h_711 : (by
              let _equal_wd_1_0 := _object_w15
              let _equal_wd_1_1 := _object_w16
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w15;
                    let _equal_wd_1_1 := _object_w16;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                      let _wd_2_1 := _value_i6;
                      let _wd_2_2 := _value_i7;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_732 h_733 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) from rfl))
                    ))).trans _litex_residual)))
                  )
              )
            let _object_w17 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i7 _value_i8 (h_177 (M := M)) h_733 h_734 True.intro)
            let _object_w18 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734))
            have h_712 : (by
              let _equal_wd_1_0 := _object_w17
              let _equal_wd_1_1 := _object_w18
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w17;
                    let _equal_wd_1_1 := _object_w18;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                      let _wd_2_1 := _value_i7;
                      let _wd_2_2 := _value_i8;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_733 h_734 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from rfl))
                    ))).trans _litex_residual)))
                  )
              )
            let _object_w19 := (let _wd_2_0 := _object_w15;
            let _wd_2_1 := _value_i8;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
              let _atomic_wd_1_0 := _object_w15
              exact (by
                let _litex_return_call := _object_w15
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_734 True.intro))
            let _object_w20 := (let _wd_2_0 := _object_w16;
            let _wd_2_1 := _value_i8;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
              let _atomic_wd_1_0 := _object_w16
              exact (Litex.addInZ _value_i6 _value_i7 h_732 h_733)) h_734 True.intro))
            have h_713 : (by
              let _equal_wd_1_0 := _object_w19
              let _equal_wd_1_1 := _object_w20
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_711 (show @Eq M.Value _ _ from Eq.refl _)))
                  )
              )
            let _object_w21 := (let _wd_2_0 := _object_w16;
            let _wd_2_1 := _value_i8;
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w16
              exact (Litex.addInC _value_i6 _value_i7 (Litex.integerToComplex _value_i6 h_732) (Litex.integerToComplex _value_i7 h_733))) (Litex.integerToComplex _wd_2_1 h_734)))
            have h_714 : (by
              let _equal_wd_1_0 := _object_w20
              let _equal_wd_1_1 := _object_w21
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from by
                      have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from by
                      let _litex_original := _object_w20
                      let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                      let _wd_2_1 := _object_w16;
                      let _wd_2_2 := _value_i8;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
                        let _atomic_wd_1_0 := _object_w16
                        exact (Litex.addInZ _value_i6 _value_i7 h_732 h_733)) h_734 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w22 := (let _wd_2_0 := _value_i6;
            let _wd_2_1 := _object_w17;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
              let _atomic_wd_1_0 := _object_w17
              exact (by
                let _litex_return_call := _object_w17
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            let _object_w23 := (let _wd_2_0 := _value_i6;
            let _wd_2_1 := _object_w18;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_732 (by
              let _atomic_wd_1_0 := _object_w18
              exact (Litex.addInZ _value_i7 _value_i8 h_733 h_734)) True.intro))
            have h_715 : (by
              let _equal_wd_1_0 := _object_w22
              let _equal_wd_1_1 := _object_w23
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_712))
                  )
              )
            let _object_w24 := (let _wd_2_0 := _value_i6;
            let _wd_2_1 := _object_w18;
            (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_732) (by
              let _atomic_wd_1_0 := _object_w18
              exact (Litex.addInC _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_733) (Litex.integerToComplex _value_i8 h_734)))))
            have h_716 : (by
              let _equal_wd_1_0 := _object_w23
              let _equal_wd_1_1 := _object_w24
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))])) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))])) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from by
                      let _litex_original := _object_w23
                      let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
                      let _wd_2_1 := _value_i6;
                      let _wd_2_2 := _object_w18;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_732 (by
                        let _atomic_wd_1_0 := _object_w18
                        exact (Litex.addInZ _value_i7 _value_i8 h_733 h_734)) True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i6) (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            have h_717 : (by
              let _equal_wd_1_0 := _object_w21
              let _equal_wd_1_1 := _object_w24
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_732)) + (Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_733))) + (Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_734))) ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_732)) + ((Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_733)) + (Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_734)))) (Litex.NativeBridge.denoteAdd (_object_w21).val.left _value_i8 (_object_w21).wd.1 (_object_w21).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i6 _value_i7 (_object_w16).wd.1 (_object_w16).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_732)) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_733))) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_734))) (Litex.NativeBridge.denoteAdd _value_i6 (_object_w24).val.right (_object_w24).wd.1 (_object_w24).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_732)) (Litex.NativeBridge.denoteAdd _value_i7 _value_i8 (_object_w18).wd.1 (_object_w18).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_733)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_734)))) (by ring!))
                  )
              )
            have h_718 : (by
              let _equal_wd_1_0 := _object_w19
              let _equal_wd_1_1 := _object_w22
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    ((((((((h_713).trans h_714)).trans h_717)).trans (h_716).symm)).trans (h_715).symm)
                  )
              )
            exact (And.intro h_711 (And.intro h_712 (And.intro h_713 (And.intro h_714 (And.intro h_715 (And.intro h_716 (And.intro h_717 h_718)))))))
          );
          let h_2368 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M)))))));
          Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) h_180 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) (h_177 (M := M))) h_182 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => True) i).mpr ⟨h_2368 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_191 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_719 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
          have _seed : Litex.denote _fold.val.seed = M.number (10 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num : (10 : ℂ) = (10 : ℂ)))
          have _members : ∀ x, M.mem x (Litex.denote _fold.val.set) ↔ x ∈ ([M.number (1 : ℂ), M.number (2 : ℂ)] : List M.Value) := (by
            let _enumerated := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            have _enumeration_same : Litex.Same (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            let _collection_tail_1 := _collection_tail_0.val.tail
            let _collection_tail_2 := _collection_tail_1.val.tail
            have _members_2 : ∀ x, M.mem x (Litex.denote _collection_tail_2) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            have _number_1 : Litex.denote _collection_tail_1.val.element = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number (2 : ℂ)) [] _number_1 _members_2
            have _number_0 : Litex.denote _collection_tail_0.val.element = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number (1 : ℂ)) [M.number (2 : ℂ)] _number_0 _members_1
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([M.number (1 : ℂ), M.number (2 : ℂ)] : List M.Value)) _enumeration_same) (_members_0 x))
          have _distinct : ([M.number (1 : ℂ), M.number (2 : ℂ)] : List M.Value).Nodup := List.Nodup.map M.number_injective (by norm_num : ([(1 : ℂ), (2 : ℂ)] : List ℂ).Nodup)
          have _term_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (1 : ℂ)) = M.number (2 : ℂ) := (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i1 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_58 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) := by change (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _call.val.argument) = (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (10 : ℂ)) (M.number (2 : ℂ))) = M.number (12 : ℂ) := (by
            let _call := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (10 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_177 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i3 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_178 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (10 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num : (10 : ℂ) = (10 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.addValue (M.number (10 : ℂ)) (M.number (2 : ℂ))) := by change (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.addValue (M.number (10 : ℂ)) (M.number (2 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.addValue (M.number (10 : ℂ)) (M.number (2 : ℂ))) = M.number (12 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (2 : ℂ)) = M.number (3 : ℂ) := (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i1 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_58 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) := by change (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _call.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (12 : ℂ)) (M.number (3 : ℂ))) = M.number (15 : ℂ) := (by
            let _call := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_177 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (12 : ℂ) (12 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i3 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_178 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (12 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = (12 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.addValue (M.number (12 : ℂ)) (M.number (3 : ℂ))) := by change (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.addValue (M.number (12 : ℂ)) (M.number (3 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.addValue (M.number (12 : ℂ)) (M.number (3 : ℂ))) = M.number (15 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          apply (Litex.finiteFoldEnumerate _fold [M.number (1 : ℂ), M.number (2 : ℂ)] _distinct _members).trans
          show Litex.foldValue [M.number (1 : ℂ), M.number (2 : ℂ)] (Litex.denote _fold.val.function) (Litex.denote _fold.val.operation) (Litex.denote _fold.val.seed) = M.number (15 : ℂ)
          norm_num [Litex.foldValue, Litex.foldApply2, _seed, _term_0, _step_0, _term_1, _step_1]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num : (15 : ℂ) = (15 : ℂ)))).symm)))
      )
  )

theorem h_6813 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_1_1 := (_object_i1 (M := M));
  let _wd_1_2 := (_object_i3 (M := M));
  let _wd_1_3 := (Litex.number (M := M) (10 : ℂ));
  (let h_4613 : (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact (let _finite_tail_0 := _atomic_wd_1_0;
    let _finite_tail_1 := _finite_tail_0.val.tail;
    let _finite_tail_2 := _finite_tail_1.val.tail;
    have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
    have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
    _finite_0));
  let h_4615 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
  let h_4624 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_4637 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_4638 : Litex.In _value_i13 (Litex.Z (M := M))), (by
    let _object_w42 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_4637 h_4638 True.intro)
    let _object_w43 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_4637) (Litex.integerToComplex _value_i13 h_4638))
    let _object_w44 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i12 (h_177 (M := M)) h_4638 h_4637 True.intro)
    let _object_w45 := (Litex.add _value_i13 _value_i12 (Litex.integerToComplex _value_i13 h_4638) (Litex.integerToComplex _value_i12 h_4637))
    exact (((by
      let _equal_wd_2_0 := _object_w42
      let _equal_wd_2_1 := _object_w43
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w44
      let _equal_wd_2_1 := _object_w45
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w43
      let _equal_wd_2_1 := _object_w45
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
      let _equal_wd_2_0 := _object_w42
      let _equal_wd_2_1 := _object_w44
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))
  ) := (by
    intro _Host_i12 _rep_i12 _value_i12 h_4637 _Host_i13 _rep_i13 _value_i13 h_4638
    let _object_w42 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_4637 h_4638 True.intro)
    let _object_w43 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_4637) (Litex.integerToComplex _value_i13 h_4638))
    have h_4620 : (by
      let _equal_wd_2_0 := _object_w42
      let _equal_wd_2_1 := _object_w43
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_2_0 := _object_w42;
            let _equal_wd_2_1 := _object_w43;
            (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
              let _litex_original := _equal_wd_2_0
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i12;
              let _wd_2_2 := _value_i13;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_4637 h_4638 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w44 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i12 (h_177 (M := M)) h_4638 h_4637 True.intro)
    let _object_w45 := (Litex.add _value_i13 _value_i12 (Litex.integerToComplex _value_i13 h_4638) (Litex.integerToComplex _value_i12 h_4637))
    have h_4621 : (by
      let _equal_wd_2_0 := _object_w44
      let _equal_wd_2_1 := _object_w45
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_2_0 := _object_w44;
            let _equal_wd_2_1 := _object_w45;
            (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i12)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i12)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) from by
              let _litex_original := _equal_wd_2_0
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i13;
              let _wd_2_2 := _value_i12;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_4638 h_4637 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i12)) from rfl))
            ))).trans _litex_residual)))
          )
      )
    have h_4622 : (by
      let _equal_wd_2_0 := _object_w43
      let _equal_wd_2_1 := _object_w45
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_4637)) + (Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_4638))) ((Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_4638)) + (Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_4637))) (Litex.NativeBridge.denoteAdd _value_i12 _value_i13 (_object_w43).wd.1 (_object_w43).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_4637)) (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_4638))) (Litex.NativeBridge.denoteAdd _value_i13 _value_i12 (_object_w45).wd.1 (_object_w45).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_4638)) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_4637))) (by ring!))
          )
      )
    have h_4623 : (by
      let _equal_wd_2_0 := _object_w42
      let _equal_wd_2_1 := _object_w44
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            ((((h_4620).trans h_4622)).trans (h_4621).symm)
          )
      )
    exact (And.intro h_4620 (And.intro h_4621 (And.intro h_4622 h_4623)))
  );
  let h_5152 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_5165 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_5166 : Litex.In _value_i13 (Litex.Z (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_5167 : Litex.In _value_i14 (Litex.Z (M := M))), (by
    let _object_w47 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_5165 h_5166 True.intro)
    let _object_w48 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))
    let _object_w49 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i14 (h_177 (M := M)) h_5166 h_5167 True.intro)
    let _object_w50 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167))
    let _object_w51 := (let _wd_2_0 := _object_w47;
    let _wd_2_1 := _value_i14;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
      let _atomic_wd_1_0 := _object_w47
      exact (by
        let _litex_return_call := _object_w47
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_5167 True.intro))
    let _object_w52 := (let _wd_2_0 := _object_w48;
    let _wd_2_1 := _value_i14;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
      let _atomic_wd_1_0 := _object_w48
      exact (Litex.addInZ _value_i12 _value_i13 h_5165 h_5166)) h_5167 True.intro))
    let _object_w53 := (let _wd_2_0 := _object_w48;
    let _wd_2_1 := _value_i14;
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _object_w48
      exact (Litex.addInC _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))) (Litex.integerToComplex _wd_2_1 h_5167)))
    let _object_w54 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w49;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
      let _atomic_wd_1_0 := _object_w49
      exact (by
        let _litex_return_call := _object_w49
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    let _object_w55 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w50;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
      let _atomic_wd_1_0 := _object_w50
      exact (Litex.addInZ _value_i13 _value_i14 h_5166 h_5167)) True.intro))
    let _object_w56 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w50;
    (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_5165) (by
      let _atomic_wd_1_0 := _object_w50
      exact (Litex.addInC _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167)))))
    exact (((by
      let _equal_wd_2_0 := _object_w47
      let _equal_wd_2_1 := _object_w48
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w49
      let _equal_wd_2_1 := _object_w50
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w51
      let _equal_wd_2_1 := _object_w52
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w52
      let _equal_wd_2_1 := _object_w53
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w54
      let _equal_wd_2_1 := _object_w55
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w55
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w53
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
      let _equal_wd_2_0 := _object_w51
      let _equal_wd_2_1 := _object_w54
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))))))))))
  ) := (by
    intro _Host_i12 _rep_i12 _value_i12 h_5165 _Host_i13 _rep_i13 _value_i13 h_5166 _Host_i14 _rep_i14 _value_i14 h_5167
    let _object_w47 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 (h_177 (M := M)) h_5165 h_5166 True.intro)
    let _object_w48 := (Litex.add _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))
    have h_5144 : (by
      let _equal_wd_2_0 := _object_w47
      let _equal_wd_2_1 := _object_w48
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_2_0 := _object_w47;
            let _equal_wd_2_1 := _object_w48;
            (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from by
              let _litex_original := _equal_wd_2_0
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i12;
              let _wd_2_2 := _value_i13;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_5165 h_5166 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w49 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i14 (h_177 (M := M)) h_5166 h_5167 True.intro)
    let _object_w50 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167))
    have h_5145 : (by
      let _equal_wd_2_0 := _object_w49
      let _equal_wd_2_1 := _object_w50
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_2_0 := _object_w49;
            let _equal_wd_2_1 := _object_w50;
            (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
              let _litex_original := _equal_wd_2_0
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i13;
              let _wd_2_2 := _value_i14;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_5166 h_5167 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w51 := (let _wd_2_0 := _object_w47;
    let _wd_2_1 := _value_i14;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
      let _atomic_wd_1_0 := _object_w47
      exact (by
        let _litex_return_call := _object_w47
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_5167 True.intro))
    let _object_w52 := (let _wd_2_0 := _object_w48;
    let _wd_2_1 := _value_i14;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) (by
      let _atomic_wd_1_0 := _object_w48
      exact (Litex.addInZ _value_i12 _value_i13 h_5165 h_5166)) h_5167 True.intro))
    have h_5146 : (by
      let _equal_wd_2_0 := _object_w51
      let _equal_wd_2_1 := _object_w52
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_5144 (show @Eq M.Value _ _ from Eq.refl _)))
          )
      )
    let _object_w53 := (let _wd_2_0 := _object_w48;
    let _wd_2_1 := _value_i14;
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _object_w48
      exact (Litex.addInC _value_i12 _value_i13 (Litex.integerToComplex _value_i12 h_5165) (Litex.integerToComplex _value_i13 h_5166))) (Litex.integerToComplex _wd_2_1 h_5167)))
    have h_5147 : (by
      let _equal_wd_2_0 := _object_w52
      let _equal_wd_2_1 := _object_w53
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)), (Litex.denote _value_i14)])) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) from by
              have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)), (Litex.denote _value_i14)])) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) from by
              let _litex_original := _object_w52
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _object_w48;
              let _wd_2_2 := _value_i14;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
                let _atomic_wd_1_0 := _object_w48
                exact (Litex.addInZ _value_i12 _value_i13 h_5165 h_5166)) h_5167 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i12) (Litex.denote _value_i13)) (Litex.denote _value_i14)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w54 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w49;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
      let _atomic_wd_1_0 := _object_w49
      exact (by
        let _litex_return_call := _object_w49
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    let _object_w55 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w50;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _wd_2_1 (h_177 (M := M)) h_5165 (by
      let _atomic_wd_1_0 := _object_w50
      exact (Litex.addInZ _value_i13 _value_i14 h_5166 h_5167)) True.intro))
    have h_5148 : (by
      let _equal_wd_2_0 := _object_w54
      let _equal_wd_2_1 := _object_w55
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_5145))
          )
      )
    let _object_w56 := (let _wd_2_0 := _value_i12;
    let _wd_2_1 := _object_w50;
    (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_5165) (by
      let _atomic_wd_1_0 := _object_w50
      exact (Litex.addInC _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_5166) (Litex.integerToComplex _value_i14 h_5167)))))
    have h_5149 : (by
      let _equal_wd_2_0 := _object_w55
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))])) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _wd_1_2) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))])) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) from by
              let _litex_original := _object_w55
              let _litex_literal := (let _wd_2_0 := (_object_i3 (M := M));
              let _wd_2_1 := _value_i12;
              let _wd_2_2 := _object_w50;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_5165 (by
                let _atomic_wd_1_0 := _object_w50
                exact (Litex.addInZ _value_i13 _value_i14 h_5166 h_5167)) True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i12) (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14))) from rfl))
            ))).trans _litex_residual)
          )
      )
    have h_5150 : (by
      let _equal_wd_2_0 := _object_w53
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_5165)) + (Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_5166))) + (Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_5167))) ((Litex.NativeBridge.asComplex _value_i12 (Litex.integerToComplex _value_i12 h_5165)) + ((Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_5166)) + (Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_5167)))) (Litex.NativeBridge.denoteAdd (_object_w53).val.left _value_i14 (_object_w53).wd.1 (_object_w53).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i12 _value_i13 (_object_w48).wd.1 (_object_w48).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_5165)) (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_5166))) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_5167))) (Litex.NativeBridge.denoteAdd _value_i12 (_object_w56).val.right (_object_w56).wd.1 (_object_w56).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.integerToComplex _value_i12 h_5165)) (Litex.NativeBridge.denoteAdd _value_i13 _value_i14 (_object_w50).wd.1 (_object_w50).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_5166)) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_5167)))) (by ring!))
          )
      )
    have h_5151 : (by
      let _equal_wd_2_0 := _object_w51
      let _equal_wd_2_1 := _object_w54
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            ((((((((h_5146).trans h_5147)).trans h_5150)).trans (h_5149).symm)).trans (h_5148).symm)
          )
      )
    exact (And.intro h_5144 (And.intro h_5145 (And.intro h_5146 (And.intro h_5147 (And.intro h_5148 (And.intro h_5149 (And.intro h_5150 h_5151)))))))
  );
  let h_6801 : (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M)))))));
  Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) h_4613 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) (h_177 (M := M))) h_4615 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => True) i).mpr ⟨h_6801 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_4624 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_5152 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (15 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_4611 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_named_x5f_fold_x2f_statement_x2e_lit
