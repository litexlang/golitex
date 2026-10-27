import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_fold_x5f_singleton_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : Litex.Same (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
  intro _raw_i1 h_6935 _
  let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_6935)
  have h_6935 : Litex.In _value_i1 (Litex.Z (M := M)) := h_6935
  change Litex.In _value_i1 (Litex.Z (M := M))
  exact h_6935));
let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
  intro _raw_i2 _raw_i3 h_6954 h_6955 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6954)
  have h_6954 : Litex.In _value_i2 (Litex.Z (M := M)) := h_6954
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6955)
  have h_6955 : Litex.In _value_i3 (Litex.Z (M := M)) := h_6955
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6954) (Litex.integerToComplex _value_i3 h_6955))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6954) (Litex.integerToComplex _value_i3 h_6955))
    exact (Litex.addInZ _value_i2 _value_i3 h_6954 h_6955))));
let _wd_1_3 := (Litex.number (M := M) (0 : ℂ));
(let h_7037 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0));
let h_7038 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
let h_7043 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_7056 : Litex.In _value_i7 (Litex.Z (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_7057 : Litex.In _value_i8 (Litex.Z (M := M))), (by
  let _object_w26 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_7071 h_7072 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7071)
    have h_7071 : Litex.In _value_i2 (Litex.Z (M := M)) := h_7071
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7072)
    have h_7072 : Litex.In _value_i3 (Litex.Z (M := M)) := h_7072
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_7071) (Litex.integerToComplex _value_i3 h_7072))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_7071) (Litex.integerToComplex _value_i3 h_7072))
      exact (Litex.addInZ _value_i2 _value_i3 h_7071 h_7072))));
  let _wd_2_1 := _value_i7;
  let _wd_2_2 := _value_i8;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7056 h_7057 True.intro))
  let _object_w27 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7056) (Litex.integerToComplex _value_i8 h_7057))
  let _object_w28 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_8171 h_8172 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8171)
    have h_8171 : Litex.In _value_i2 (Litex.Z (M := M)) := h_8171
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8172)
    have h_8172 : Litex.In _value_i3 (Litex.Z (M := M)) := h_8172
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_8171) (Litex.integerToComplex _value_i3 h_8172))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_8171) (Litex.integerToComplex _value_i3 h_8172))
      exact (Litex.addInZ _value_i2 _value_i3 h_8171 h_8172))));
  let _wd_2_1 := _value_i8;
  let _wd_2_2 := _value_i7;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7057 h_7056 True.intro))
  let _object_w29 := (Litex.add _value_i8 _value_i7 (Litex.integerToComplex _value_i8 h_7057) (Litex.integerToComplex _value_i7 h_7056))
  exact (((by
    let _equal_wd_1_0 := _object_w26
    let _equal_wd_1_1 := _object_w27
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w28
    let _equal_wd_1_1 := _object_w29
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w27
    let _equal_wd_1_1 := _object_w29
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w26
    let _equal_wd_1_1 := _object_w28
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
) := (by
  intro _Host_i7 _rep_i7 _value_i7 h_7056 _Host_i8 _rep_i8 _value_i8 h_7057
  let _object_w26 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_7071 h_7072 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7071)
    have h_7071 : Litex.In _value_i2 (Litex.Z (M := M)) := h_7071
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7072)
    have h_7072 : Litex.In _value_i3 (Litex.Z (M := M)) := h_7072
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_7071) (Litex.integerToComplex _value_i3 h_7072))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_7071) (Litex.integerToComplex _value_i3 h_7072))
      exact (Litex.addInZ _value_i2 _value_i3 h_7071 h_7072))));
  let _wd_2_1 := _value_i7;
  let _wd_2_2 := _value_i8;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7056 h_7057 True.intro))
  let _object_w27 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7056) (Litex.integerToComplex _value_i8 h_7057))
  have h_7039 : (by
    let _equal_wd_1_0 := _object_w26
    let _equal_wd_1_1 := _object_w27
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_7810 h_7811 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7810)
              have h_7810 : Litex.In _value_i2 (Litex.Z (M := M)) := h_7810
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7811)
              have h_7811 : Litex.In _value_i3 (Litex.Z (M := M)) := h_7811
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_7810) (Litex.integerToComplex _value_i3 h_7811))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_7810) (Litex.integerToComplex _value_i3 h_7811))
                exact (Litex.addInZ _value_i2 _value_i3 h_7810 h_7811))));
            let _wd_2_1 := _value_i7;
            let _wd_2_2 := _value_i8;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7056 h_7057 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_7957 h_7958 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7957)
              have h_7957 : Litex.In _value_i2 (Litex.Z (M := M)) := h_7957
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7958)
              have h_7958 : Litex.In _value_i3 (Litex.Z (M := M)) := h_7958
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_7957) (Litex.integerToComplex _value_i3 h_7958))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_7957) (Litex.integerToComplex _value_i3 h_7958))
                exact (Litex.addInZ _value_i2 _value_i3 h_7957 h_7958))));
            let _wd_2_1 := _value_i7;
            let _wd_2_2 := _value_i8;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7056 h_7057 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w28 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_8171 h_8172 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8171)
    have h_8171 : Litex.In _value_i2 (Litex.Z (M := M)) := h_8171
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8172)
    have h_8172 : Litex.In _value_i3 (Litex.Z (M := M)) := h_8172
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_8171) (Litex.integerToComplex _value_i3 h_8172))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_8171) (Litex.integerToComplex _value_i3 h_8172))
      exact (Litex.addInZ _value_i2 _value_i3 h_8171 h_8172))));
  let _wd_2_1 := _value_i8;
  let _wd_2_2 := _value_i7;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7057 h_7056 True.intro))
  let _object_w29 := (Litex.add _value_i8 _value_i7 (Litex.integerToComplex _value_i8 h_7057) (Litex.integerToComplex _value_i7 h_7056))
  have h_7040 : (by
    let _equal_wd_1_0 := _object_w28
    let _equal_wd_1_1 := _object_w29
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i7)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i7)) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i7)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i7)])) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i7)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_8910 h_8911 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8910)
              have h_8910 : Litex.In _value_i2 (Litex.Z (M := M)) := h_8910
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8911)
              have h_8911 : Litex.In _value_i3 (Litex.Z (M := M)) := h_8911
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_8910) (Litex.integerToComplex _value_i3 h_8911))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_8910) (Litex.integerToComplex _value_i3 h_8911))
                exact (Litex.addInZ _value_i2 _value_i3 h_8910 h_8911))));
            let _wd_2_1 := _value_i8;
            let _wd_2_2 := _value_i7;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7057 h_7056 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_9057 h_9058 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9057)
              have h_9057 : Litex.In _value_i2 (Litex.Z (M := M)) := h_9057
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9058)
              have h_9058 : Litex.In _value_i3 (Litex.Z (M := M)) := h_9058
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_9057) (Litex.integerToComplex _value_i3 h_9058))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_9057) (Litex.integerToComplex _value_i3 h_9058))
                exact (Litex.addInZ _value_i2 _value_i3 h_9057 h_9058))));
            let _wd_2_1 := _value_i8;
            let _wd_2_2 := _value_i7;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7057 h_7056 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i7)) from rfl))
          ))).trans _litex_residual)
        )
    )
  have h_7041 : (by
    let _equal_wd_1_0 := _object_w27
    let _equal_wd_1_1 := _object_w29
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_7056)) + (Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_7057))) ((Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_7057)) + (Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_7056))) (Litex.NativeBridge.denoteAdd _value_i7 _value_i8 (_object_w27).wd.1 (_object_w27).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_7056)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_7057))) (Litex.NativeBridge.denoteAdd _value_i8 _value_i7 (_object_w29).wd.1 (_object_w29).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_7057)) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_7056))) (by ring!))
        )
    )
  have h_7042 : (by
    let _equal_wd_1_0 := _object_w26
    let _equal_wd_1_1 := _object_w28
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          ((((h_7039).trans h_7041)).trans (h_7040).symm)
        )
    )
  exact (And.intro h_7039 (And.intro h_7040 (And.intro h_7041 h_7042)))
);
let h_9271 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_9284 : Litex.In _value_i7 (Litex.Z (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_9285 : Litex.In _value_i8 (Litex.Z (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_9286 : Litex.In _value_i9 (Litex.Z (M := M))), (by
  let _object_w31 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_9300 h_9301 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9300)
    have h_9300 : Litex.In _value_i2 (Litex.Z (M := M)) := h_9300
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9301)
    have h_9301 : Litex.In _value_i3 (Litex.Z (M := M)) := h_9301
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_9300) (Litex.integerToComplex _value_i3 h_9301))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_9300) (Litex.integerToComplex _value_i3 h_9301))
      exact (Litex.addInZ _value_i2 _value_i3 h_9300 h_9301))));
  let _wd_2_1 := _value_i7;
  let _wd_2_2 := _value_i8;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9284 h_9285 True.intro))
  let _object_w32 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_9284) (Litex.integerToComplex _value_i8 h_9285))
  let _object_w33 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_10564 h_10565 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_10564)
    have h_10564 : Litex.In _value_i2 (Litex.Z (M := M)) := h_10564
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10565)
    have h_10565 : Litex.In _value_i3 (Litex.Z (M := M)) := h_10565
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_10564) (Litex.integerToComplex _value_i3 h_10565))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_10564) (Litex.integerToComplex _value_i3 h_10565))
      exact (Litex.addInZ _value_i2 _value_i3 h_10564 h_10565))));
  let _wd_2_1 := _value_i8;
  let _wd_2_2 := _value_i9;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9285 h_9286 True.intro))
  let _object_w34 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_9285) (Litex.integerToComplex _value_i9 h_9286))
  let _object_w35 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_11856 h_11857 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_11856)
    have h_11856 : Litex.In _value_i2 (Litex.Z (M := M)) := h_11856
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11857)
    have h_11857 : Litex.In _value_i3 (Litex.Z (M := M)) := h_11857
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_11856) (Litex.integerToComplex _value_i3 h_11857))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_11856) (Litex.integerToComplex _value_i3 h_11857))
      exact (Litex.addInZ _value_i2 _value_i3 h_11856 h_11857))));
  let _wd_2_1 := _object_w31;
  let _wd_2_2 := _value_i9;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w31
    exact (Litex.inOfSame _object_w31 _object_w31 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w31) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w31))) h_9286 True.intro))
  let _object_w36 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_12058 h_12059 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12058)
    have h_12058 : Litex.In _value_i2 (Litex.Z (M := M)) := h_12058
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_12059)
    have h_12059 : Litex.In _value_i3 (Litex.Z (M := M)) := h_12059
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12058) (Litex.integerToComplex _value_i3 h_12059))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12058) (Litex.integerToComplex _value_i3 h_12059))
      exact (Litex.addInZ _value_i2 _value_i3 h_12058 h_12059))));
  let _wd_2_1 := _object_w32;
  let _wd_2_2 := _value_i9;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w32
    exact (Litex.addInZ _value_i7 _value_i8 h_9284 h_9285)) h_9286 True.intro))
  let _object_w37 := (let _wd_2_0 := _object_w32;
  let _wd_2_1 := _value_i9;
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _object_w32
    exact (Litex.addInC _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_9284) (Litex.integerToComplex _value_i8 h_9285))) (Litex.integerToComplex _wd_2_1 h_9286)))
  let _object_w38 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_12792 h_12793 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12792)
    have h_12792 : Litex.In _value_i2 (Litex.Z (M := M)) := h_12792
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_12793)
    have h_12793 : Litex.In _value_i3 (Litex.Z (M := M)) := h_12793
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12792) (Litex.integerToComplex _value_i3 h_12793))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12792) (Litex.integerToComplex _value_i3 h_12793))
      exact (Litex.addInZ _value_i2 _value_i3 h_12792 h_12793))));
  let _wd_2_1 := _value_i7;
  let _wd_2_2 := _object_w33;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9284 (by
    let _atomic_wd_1_0 := _object_w33
    exact (Litex.inOfSame _object_w33 _object_w33 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w33) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w33))) True.intro))
  let _object_w39 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_12990 h_12991 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12990)
    have h_12990 : Litex.In _value_i2 (Litex.Z (M := M)) := h_12990
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_12991)
    have h_12991 : Litex.In _value_i3 (Litex.Z (M := M)) := h_12991
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12990) (Litex.integerToComplex _value_i3 h_12991))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12990) (Litex.integerToComplex _value_i3 h_12991))
      exact (Litex.addInZ _value_i2 _value_i3 h_12990 h_12991))));
  let _wd_2_1 := _value_i7;
  let _wd_2_2 := _object_w34;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9284 (by
    let _atomic_wd_1_0 := _object_w34
    exact (Litex.addInZ _value_i8 _value_i9 h_9285 h_9286)) True.intro))
  let _object_w40 := (let _wd_2_0 := _value_i7;
  let _wd_2_1 := _object_w34;
  (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_9284) (by
    let _atomic_wd_1_0 := _object_w34
    exact (Litex.addInC _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_9285) (Litex.integerToComplex _value_i9 h_9286)))))
  exact (((by
    let _equal_wd_1_0 := _object_w31
    let _equal_wd_1_1 := _object_w32
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w33
    let _equal_wd_1_1 := _object_w34
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w35
    let _equal_wd_1_1 := _object_w36
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w36
    let _equal_wd_1_1 := _object_w37
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w38
    let _equal_wd_1_1 := _object_w39
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w39
    let _equal_wd_1_1 := _object_w40
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w37
    let _equal_wd_1_1 := _object_w40
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w35
    let _equal_wd_1_1 := _object_w38
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
) := (by
  intro _Host_i7 _rep_i7 _value_i7 h_9284 _Host_i8 _rep_i8 _value_i8 h_9285 _Host_i9 _rep_i9 _value_i9 h_9286
  let _object_w31 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_9300 h_9301 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9300)
    have h_9300 : Litex.In _value_i2 (Litex.Z (M := M)) := h_9300
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9301)
    have h_9301 : Litex.In _value_i3 (Litex.Z (M := M)) := h_9301
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_9300) (Litex.integerToComplex _value_i3 h_9301))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_9300) (Litex.integerToComplex _value_i3 h_9301))
      exact (Litex.addInZ _value_i2 _value_i3 h_9300 h_9301))));
  let _wd_2_1 := _value_i7;
  let _wd_2_2 := _value_i8;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9284 h_9285 True.intro))
  let _object_w32 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_9284) (Litex.integerToComplex _value_i8 h_9285))
  have h_9263 : (by
    let _equal_wd_1_0 := _object_w31
    let _equal_wd_1_1 := _object_w32
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_10147 h_10148 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_10147)
              have h_10147 : Litex.In _value_i2 (Litex.Z (M := M)) := h_10147
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10148)
              have h_10148 : Litex.In _value_i3 (Litex.Z (M := M)) := h_10148
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_10147) (Litex.integerToComplex _value_i3 h_10148))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_10147) (Litex.integerToComplex _value_i3 h_10148))
                exact (Litex.addInZ _value_i2 _value_i3 h_10147 h_10148))));
            let _wd_2_1 := _value_i7;
            let _wd_2_2 := _value_i8;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9284 h_9285 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_10314 h_10315 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_10314)
              have h_10314 : Litex.In _value_i2 (Litex.Z (M := M)) := h_10314
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10315)
              have h_10315 : Litex.In _value_i3 (Litex.Z (M := M)) := h_10315
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_10314) (Litex.integerToComplex _value_i3 h_10315))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_10314) (Litex.integerToComplex _value_i3 h_10315))
                exact (Litex.addInZ _value_i2 _value_i3 h_10314 h_10315))));
            let _wd_2_1 := _value_i7;
            let _wd_2_2 := _value_i8;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9284 h_9285 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w33 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_10564 h_10565 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_10564)
    have h_10564 : Litex.In _value_i2 (Litex.Z (M := M)) := h_10564
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10565)
    have h_10565 : Litex.In _value_i3 (Litex.Z (M := M)) := h_10565
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_10564) (Litex.integerToComplex _value_i3 h_10565))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_10564) (Litex.integerToComplex _value_i3 h_10565))
      exact (Litex.addInZ _value_i2 _value_i3 h_10564 h_10565))));
  let _wd_2_1 := _value_i8;
  let _wd_2_2 := _value_i9;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9285 h_9286 True.intro))
  let _object_w34 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_9285) (Litex.integerToComplex _value_i9 h_9286))
  have h_9264 : (by
    let _equal_wd_1_0 := _object_w33
    let _equal_wd_1_1 := _object_w34
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i9)])) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i9)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i9)])) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_11431 h_11432 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_11431)
              have h_11431 : Litex.In _value_i2 (Litex.Z (M := M)) := h_11431
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11432)
              have h_11432 : Litex.In _value_i3 (Litex.Z (M := M)) := h_11432
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_11431) (Litex.integerToComplex _value_i3 h_11432))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_11431) (Litex.integerToComplex _value_i3 h_11432))
                exact (Litex.addInZ _value_i2 _value_i3 h_11431 h_11432))));
            let _wd_2_1 := _value_i8;
            let _wd_2_2 := _value_i9;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9285 h_9286 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_11602 h_11603 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_11602)
              have h_11602 : Litex.In _value_i2 (Litex.Z (M := M)) := h_11602
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11603)
              have h_11603 : Litex.In _value_i3 (Litex.Z (M := M)) := h_11603
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_11602) (Litex.integerToComplex _value_i3 h_11603))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_11602) (Litex.integerToComplex _value_i3 h_11603))
                exact (Litex.addInZ _value_i2 _value_i3 h_11602 h_11603))));
            let _wd_2_1 := _value_i8;
            let _wd_2_2 := _value_i9;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9285 h_9286 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w35 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_11856 h_11857 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_11856)
    have h_11856 : Litex.In _value_i2 (Litex.Z (M := M)) := h_11856
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11857)
    have h_11857 : Litex.In _value_i3 (Litex.Z (M := M)) := h_11857
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_11856) (Litex.integerToComplex _value_i3 h_11857))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_11856) (Litex.integerToComplex _value_i3 h_11857))
      exact (Litex.addInZ _value_i2 _value_i3 h_11856 h_11857))));
  let _wd_2_1 := _object_w31;
  let _wd_2_2 := _value_i9;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w31
    exact (Litex.inOfSame _object_w31 _object_w31 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w31) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w31))) h_9286 True.intro))
  let _object_w36 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_12058 h_12059 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12058)
    have h_12058 : Litex.In _value_i2 (Litex.Z (M := M)) := h_12058
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_12059)
    have h_12059 : Litex.In _value_i3 (Litex.Z (M := M)) := h_12059
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12058) (Litex.integerToComplex _value_i3 h_12059))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12058) (Litex.integerToComplex _value_i3 h_12059))
      exact (Litex.addInZ _value_i2 _value_i3 h_12058 h_12059))));
  let _wd_2_1 := _object_w32;
  let _wd_2_2 := _value_i9;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w32
    exact (Litex.addInZ _value_i7 _value_i8 h_9284 h_9285)) h_9286 True.intro))
  have h_9265 : (by
    let _equal_wd_1_0 := _object_w35
    let _equal_wd_1_1 := _object_w36
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_9263 (show @Eq M.Value _ _ from Eq.refl _)))
        )
    )
  let _object_w37 := (let _wd_2_0 := _object_w32;
  let _wd_2_1 := _value_i9;
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _object_w32
    exact (Litex.addInC _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_9284) (Litex.integerToComplex _value_i8 h_9285))) (Litex.integerToComplex _wd_2_1 h_9286)))
  have h_9266 : (by
    let _equal_wd_1_0 := _object_w36
    let _equal_wd_1_1 := _object_w37
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)), (Litex.denote _value_i9)])) = (M.addValue (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) (Litex.denote _value_i9)) from by
            have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) (Litex.denote _value_i9)) = (M.addValue (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)), (Litex.denote _value_i9)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)), (Litex.denote _value_i9)])) = (M.addValue (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) (Litex.denote _value_i9)) from by
            let _litex_original := _object_w36
            let _litex_literal := _object_w36
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) (Litex.denote _value_i9)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w38 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_12792 h_12793 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12792)
    have h_12792 : Litex.In _value_i2 (Litex.Z (M := M)) := h_12792
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_12793)
    have h_12793 : Litex.In _value_i3 (Litex.Z (M := M)) := h_12793
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12792) (Litex.integerToComplex _value_i3 h_12793))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12792) (Litex.integerToComplex _value_i3 h_12793))
      exact (Litex.addInZ _value_i2 _value_i3 h_12792 h_12793))));
  let _wd_2_1 := _value_i7;
  let _wd_2_2 := _object_w33;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9284 (by
    let _atomic_wd_1_0 := _object_w33
    exact (Litex.inOfSame _object_w33 _object_w33 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w33) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w33))) True.intro))
  let _object_w39 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_12990 h_12991 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12990)
    have h_12990 : Litex.In _value_i2 (Litex.Z (M := M)) := h_12990
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_12991)
    have h_12991 : Litex.In _value_i3 (Litex.Z (M := M)) := h_12991
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12990) (Litex.integerToComplex _value_i3 h_12991))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_12990) (Litex.integerToComplex _value_i3 h_12991))
      exact (Litex.addInZ _value_i2 _value_i3 h_12990 h_12991))));
  let _wd_2_1 := _value_i7;
  let _wd_2_2 := _object_w34;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9284 (by
    let _atomic_wd_1_0 := _object_w34
    exact (Litex.addInZ _value_i8 _value_i9 h_9285 h_9286)) True.intro))
  have h_9267 : (by
    let _equal_wd_1_0 := _object_w38
    let _equal_wd_1_1 := _object_w39
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_9264))
        )
    )
  let _object_w40 := (let _wd_2_0 := _value_i7;
  let _wd_2_1 := _object_w34;
  (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_9284) (by
    let _atomic_wd_1_0 := _object_w34
    exact (Litex.addInC _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_9285) (Litex.integerToComplex _value_i9 h_9286)))))
  have h_9268 : (by
    let _equal_wd_1_0 := _object_w39
    let _equal_wd_1_1 := _object_w40
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9))])) = (M.addValue (Litex.denote _value_i7) (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9))) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i7) (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9))) = (M.addValue (Litex.denote _value_i7) (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9))])) = (M.addValue (Litex.denote _value_i7) (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9))) from by
            let _litex_original := _object_w39
            let _litex_literal := _object_w39
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9))) from rfl))
          ))).trans _litex_residual)
        )
    )
  have h_9269 : (by
    let _equal_wd_1_0 := _object_w37
    let _equal_wd_1_1 := _object_w40
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_9284)) + (Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_9285))) + (Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_9286))) ((Litex.NativeBridge.asComplex _value_i7 (Litex.integerToComplex _value_i7 h_9284)) + ((Litex.NativeBridge.asComplex _value_i8 (Litex.integerToComplex _value_i8 h_9285)) + (Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_9286)))) (Litex.NativeBridge.denoteAdd (_object_w37).val.left _value_i9 (_object_w37).wd.1 (_object_w37).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i7 _value_i8 (_object_w32).wd.1 (_object_w32).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_9284)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_9285))) (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_9286))) (Litex.NativeBridge.denoteAdd _value_i7 (_object_w40).val.right (_object_w40).wd.1 (_object_w40).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.integerToComplex _value_i7 h_9284)) (Litex.NativeBridge.denoteAdd _value_i8 _value_i9 (_object_w34).wd.1 (_object_w34).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.integerToComplex _value_i8 h_9285)) (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_9286)))) (by ring!))
        )
    )
  have h_9270 : (by
    let _equal_wd_1_0 := _object_w35
    let _equal_wd_1_1 := _object_w38
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          ((((((((h_9265).trans h_9266)).trans h_9269)).trans (h_9268).symm)).trans (h_9267).symm)
        )
    )
  exact (And.intro h_9263 (And.intro h_9264 (And.intro h_9265 (And.intro h_9266 (And.intro h_9267 (And.intro h_9268 (And.intro h_9269 h_9270)))))))
);
let h_13714 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M))))));
Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_7037 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_7038 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) i).mpr ⟨h_13714 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_7043 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_9271 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2)))))))))))))))) (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
  intro _raw_i2 _raw_i3 h_13729 h_13730 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_13729)
  have h_13729 : Litex.In _value_i2 (Litex.Z (M := M)) := h_13729
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13730)
  have h_13730 : Litex.In _value_i3 (Litex.Z (M := M)) := h_13730
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_13729) (Litex.integerToComplex _value_i3 h_13730))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_13729) (Litex.integerToComplex _value_i3 h_13730))
    exact (Litex.addInZ _value_i2 _value_i3 h_13729 h_13730))));
let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
let _object_w43 := (let _wd_2_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
  intro _raw_i1 h_13825 _
  let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_13825)
  have h_13825 : Litex.In _value_i1 (Litex.Z (M := M)) := h_13825
  change Litex.In _value_i1 (Litex.Z (M := M))
  exact h_13825));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro));
(Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _object_w43 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (by
  let _atomic_wd_1_0 := _object_w43
  exact (Litex.inOfSame _object_w43 _object_w43 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w43) (Litex.sameRefl (Litex.Z (M := M))) (Litex.callInOutput _object_w43))) True.intro)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1 : (by
            let _equal_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            let _equal_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show @Eq M.Value _ _ from Eq.refl _)
                )
            )
          exact (show (by
          let _equal_wd_1_0 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_17 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_17)
            have h_17 : Litex.In _value_i1 (Litex.Z (M := M)) := h_17
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_17));
          let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_36 h_37 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_36)
            have h_36 : Litex.In _value_i2 (Litex.Z (M := M)) := h_36
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_37)
            have h_37 : Litex.In _value_i3 (Litex.Z (M := M)) := h_37
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_36) (Litex.integerToComplex _value_i3 h_37))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_36) (Litex.integerToComplex _value_i3 h_37))
              exact (Litex.addInZ _value_i2 _value_i3 h_36 h_37))));
          let _wd_1_3 := (Litex.number (M := M) (0 : ℂ));
          (let h_119 : (by
            let _atomic_wd_1_0 := _wd_1_0
            exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0));
          let h_120 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
          let h_125 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_138 : Litex.In _value_i4 (Litex.Z (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_139 : Litex.In _value_i5 (Litex.Z (M := M))), (by
            let _object_w5 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_153 h_154 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_153)
              have h_153 : Litex.In _value_i2 (Litex.Z (M := M)) := h_153
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_154)
              have h_154 : Litex.In _value_i3 (Litex.Z (M := M)) := h_154
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_153) (Litex.integerToComplex _value_i3 h_154))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_153) (Litex.integerToComplex _value_i3 h_154))
                exact (Litex.addInZ _value_i2 _value_i3 h_153 h_154))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _value_i5;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_138 h_139 True.intro))
            let _object_w6 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_138) (Litex.integerToComplex _value_i5 h_139))
            let _object_w7 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_1253 h_1254 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1253)
              have h_1253 : Litex.In _value_i2 (Litex.Z (M := M)) := h_1253
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1254)
              have h_1254 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1254
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1253) (Litex.integerToComplex _value_i3 h_1254))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1253) (Litex.integerToComplex _value_i3 h_1254))
                exact (Litex.addInZ _value_i2 _value_i3 h_1253 h_1254))));
            let _wd_2_1 := _value_i5;
            let _wd_2_2 := _value_i4;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_138 True.intro))
            let _object_w8 := (Litex.add _value_i5 _value_i4 (Litex.integerToComplex _value_i5 h_139) (Litex.integerToComplex _value_i4 h_138))
            exact (((by
              let _equal_wd_2_0 := _object_w5
              let _equal_wd_2_1 := _object_w6
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
              let _equal_wd_2_0 := _object_w7
              let _equal_wd_2_1 := _object_w8
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
              let _equal_wd_2_0 := _object_w6
              let _equal_wd_2_1 := _object_w8
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
              let _equal_wd_2_0 := _object_w5
              let _equal_wd_2_1 := _object_w7
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))
          ) := (by
            intro _Host_i4 _rep_i4 _value_i4 h_138 _Host_i5 _rep_i5 _value_i5 h_139
            let _object_w5 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_153 h_154 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_153)
              have h_153 : Litex.In _value_i2 (Litex.Z (M := M)) := h_153
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_154)
              have h_154 : Litex.In _value_i3 (Litex.Z (M := M)) := h_154
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_153) (Litex.integerToComplex _value_i3 h_154))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_153) (Litex.integerToComplex _value_i3 h_154))
                exact (Litex.addInZ _value_i2 _value_i3 h_153 h_154))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _value_i5;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_138 h_139 True.intro))
            let _object_w6 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_138) (Litex.integerToComplex _value_i5 h_139))
            have h_121 : (by
              let _equal_wd_2_0 := _object_w5
              let _equal_wd_2_1 := _object_w6
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_892 h_893 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_892)
                        have h_892 : Litex.In _value_i2 (Litex.Z (M := M)) := h_892
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_893)
                        have h_893 : Litex.In _value_i3 (Litex.Z (M := M)) := h_893
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_892) (Litex.integerToComplex _value_i3 h_893))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_892) (Litex.integerToComplex _value_i3 h_893))
                          exact (Litex.addInZ _value_i2 _value_i3 h_892 h_893))));
                      let _wd_2_1 := _value_i4;
                      let _wd_2_2 := _value_i5;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_138 h_139 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_1039 h_1040 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1039)
                        have h_1039 : Litex.In _value_i2 (Litex.Z (M := M)) := h_1039
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1040)
                        have h_1040 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1040
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1039) (Litex.integerToComplex _value_i3 h_1040))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1039) (Litex.integerToComplex _value_i3 h_1040))
                          exact (Litex.addInZ _value_i2 _value_i3 h_1039 h_1040))));
                      let _wd_2_1 := _value_i4;
                      let _wd_2_2 := _value_i5;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_138 h_139 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w7 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_1253 h_1254 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1253)
              have h_1253 : Litex.In _value_i2 (Litex.Z (M := M)) := h_1253
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1254)
              have h_1254 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1254
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1253) (Litex.integerToComplex _value_i3 h_1254))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1253) (Litex.integerToComplex _value_i3 h_1254))
                exact (Litex.addInZ _value_i2 _value_i3 h_1253 h_1254))));
            let _wd_2_1 := _value_i5;
            let _wd_2_2 := _value_i4;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_138 True.intro))
            let _object_w8 := (Litex.add _value_i5 _value_i4 (Litex.integerToComplex _value_i5 h_139) (Litex.integerToComplex _value_i4 h_138))
            have h_122 : (by
              let _equal_wd_2_0 := _object_w7
              let _equal_wd_2_1 := _object_w8
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_1992 h_1993 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1992)
                        have h_1992 : Litex.In _value_i2 (Litex.Z (M := M)) := h_1992
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1993)
                        have h_1993 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1993
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1992) (Litex.integerToComplex _value_i3 h_1993))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1992) (Litex.integerToComplex _value_i3 h_1993))
                          exact (Litex.addInZ _value_i2 _value_i3 h_1992 h_1993))));
                      let _wd_2_1 := _value_i5;
                      let _wd_2_2 := _value_i4;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_138 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_2139 h_2140 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2139)
                        have h_2139 : Litex.In _value_i2 (Litex.Z (M := M)) := h_2139
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2140)
                        have h_2140 : Litex.In _value_i3 (Litex.Z (M := M)) := h_2140
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2139) (Litex.integerToComplex _value_i3 h_2140))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2139) (Litex.integerToComplex _value_i3 h_2140))
                          exact (Litex.addInZ _value_i2 _value_i3 h_2139 h_2140))));
                      let _wd_2_1 := _value_i5;
                      let _wd_2_2 := _value_i4;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_138 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            have h_123 : (by
              let _equal_wd_2_0 := _object_w6
              let _equal_wd_2_1 := _object_w8
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i4 (Litex.integerToComplex _value_i4 h_138)) + (Litex.NativeBridge.asComplex _value_i5 (Litex.integerToComplex _value_i5 h_139))) ((Litex.NativeBridge.asComplex _value_i5 (Litex.integerToComplex _value_i5 h_139)) + (Litex.NativeBridge.asComplex _value_i4 (Litex.integerToComplex _value_i4 h_138))) (Litex.NativeBridge.denoteAdd _value_i4 _value_i5 (_object_w6).wd.1 (_object_w6).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.integerToComplex _value_i4 h_138)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.integerToComplex _value_i5 h_139))) (Litex.NativeBridge.denoteAdd _value_i5 _value_i4 (_object_w8).wd.1 (_object_w8).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.integerToComplex _value_i5 h_139)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.integerToComplex _value_i4 h_138))) (by ring!))
                  )
              )
            have h_124 : (by
              let _equal_wd_2_0 := _object_w5
              let _equal_wd_2_1 := _object_w7
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    ((((h_121).trans h_123)).trans (h_122).symm)
                  )
              )
            exact (And.intro h_121 (And.intro h_122 (And.intro h_123 h_124)))
          );
          let h_2353 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_2366 : Litex.In _value_i4 (Litex.Z (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_2367 : Litex.In _value_i5 (Litex.Z (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_2368 : Litex.In _value_i6 (Litex.Z (M := M))), (by
            let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_2382 h_2383 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2382)
              have h_2382 : Litex.In _value_i2 (Litex.Z (M := M)) := h_2382
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2383)
              have h_2383 : Litex.In _value_i3 (Litex.Z (M := M)) := h_2383
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2382) (Litex.integerToComplex _value_i3 h_2383))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2382) (Litex.integerToComplex _value_i3 h_2383))
                exact (Litex.addInZ _value_i2 _value_i3 h_2382 h_2383))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _value_i5;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 h_2367 True.intro))
            let _object_w11 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_2366) (Litex.integerToComplex _value_i5 h_2367))
            let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_3646 h_3647 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3646)
              have h_3646 : Litex.In _value_i2 (Litex.Z (M := M)) := h_3646
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3647)
              have h_3647 : Litex.In _value_i3 (Litex.Z (M := M)) := h_3647
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3646) (Litex.integerToComplex _value_i3 h_3647))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3646) (Litex.integerToComplex _value_i3 h_3647))
                exact (Litex.addInZ _value_i2 _value_i3 h_3646 h_3647))));
            let _wd_2_1 := _value_i5;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2367 h_2368 True.intro))
            let _object_w13 := (Litex.add _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_2367) (Litex.integerToComplex _value_i6 h_2368))
            let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_4938 h_4939 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4938)
              have h_4938 : Litex.In _value_i2 (Litex.Z (M := M)) := h_4938
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4939)
              have h_4939 : Litex.In _value_i3 (Litex.Z (M := M)) := h_4939
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4938) (Litex.integerToComplex _value_i3 h_4939))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4938) (Litex.integerToComplex _value_i3 h_4939))
                exact (Litex.addInZ _value_i2 _value_i3 h_4938 h_4939))));
            let _wd_2_1 := _object_w10;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w10
              exact (Litex.inOfSame _object_w10 _object_w10 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w10) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w10))) h_2368 True.intro))
            let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_5140 h_5141 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5140)
              have h_5140 : Litex.In _value_i2 (Litex.Z (M := M)) := h_5140
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5141)
              have h_5141 : Litex.In _value_i3 (Litex.Z (M := M)) := h_5141
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5140) (Litex.integerToComplex _value_i3 h_5141))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5140) (Litex.integerToComplex _value_i3 h_5141))
                exact (Litex.addInZ _value_i2 _value_i3 h_5140 h_5141))));
            let _wd_2_1 := _object_w11;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.addInZ _value_i4 _value_i5 h_2366 h_2367)) h_2368 True.intro))
            let _object_w16 := (let _wd_2_0 := _object_w11;
            let _wd_2_1 := _value_i6;
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.addInC _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_2366) (Litex.integerToComplex _value_i5 h_2367))) (Litex.integerToComplex _wd_2_1 h_2368)))
            let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_5874 h_5875 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5874)
              have h_5874 : Litex.In _value_i2 (Litex.Z (M := M)) := h_5874
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5875)
              have h_5875 : Litex.In _value_i3 (Litex.Z (M := M)) := h_5875
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5874) (Litex.integerToComplex _value_i3 h_5875))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5874) (Litex.integerToComplex _value_i3 h_5875))
                exact (Litex.addInZ _value_i2 _value_i3 h_5874 h_5875))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _object_w12;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 (by
              let _atomic_wd_1_0 := _object_w12
              exact (Litex.inOfSame _object_w12 _object_w12 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w12) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w12))) True.intro))
            let _object_w18 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_6072 h_6073 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6072)
              have h_6072 : Litex.In _value_i2 (Litex.Z (M := M)) := h_6072
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6073)
              have h_6073 : Litex.In _value_i3 (Litex.Z (M := M)) := h_6073
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6072) (Litex.integerToComplex _value_i3 h_6073))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6072) (Litex.integerToComplex _value_i3 h_6073))
                exact (Litex.addInZ _value_i2 _value_i3 h_6072 h_6073))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _object_w13;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 (by
              let _atomic_wd_1_0 := _object_w13
              exact (Litex.addInZ _value_i5 _value_i6 h_2367 h_2368)) True.intro))
            let _object_w19 := (let _wd_2_0 := _value_i4;
            let _wd_2_1 := _object_w13;
            (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2366) (by
              let _atomic_wd_1_0 := _object_w13
              exact (Litex.addInC _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_2367) (Litex.integerToComplex _value_i6 h_2368)))))
            exact (((by
              let _equal_wd_2_0 := _object_w10
              let _equal_wd_2_1 := _object_w11
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
              let _equal_wd_2_0 := _object_w12
              let _equal_wd_2_1 := _object_w13
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
              let _equal_wd_2_0 := _object_w14
              let _equal_wd_2_1 := _object_w15
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
              let _equal_wd_2_0 := _object_w15
              let _equal_wd_2_1 := _object_w16
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
              let _equal_wd_2_0 := _object_w17
              let _equal_wd_2_1 := _object_w18
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
              let _equal_wd_2_0 := _object_w18
              let _equal_wd_2_1 := _object_w19
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
              let _equal_wd_2_0 := _object_w16
              let _equal_wd_2_1 := _object_w19
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
              let _equal_wd_2_0 := _object_w14
              let _equal_wd_2_1 := _object_w17
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))))))))))
          ) := (by
            intro _Host_i4 _rep_i4 _value_i4 h_2366 _Host_i5 _rep_i5 _value_i5 h_2367 _Host_i6 _rep_i6 _value_i6 h_2368
            let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_2382 h_2383 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2382)
              have h_2382 : Litex.In _value_i2 (Litex.Z (M := M)) := h_2382
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2383)
              have h_2383 : Litex.In _value_i3 (Litex.Z (M := M)) := h_2383
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2382) (Litex.integerToComplex _value_i3 h_2383))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2382) (Litex.integerToComplex _value_i3 h_2383))
                exact (Litex.addInZ _value_i2 _value_i3 h_2382 h_2383))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _value_i5;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 h_2367 True.intro))
            let _object_w11 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_2366) (Litex.integerToComplex _value_i5 h_2367))
            have h_2345 : (by
              let _equal_wd_2_0 := _object_w10
              let _equal_wd_2_1 := _object_w11
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_3229 h_3230 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3229)
                        have h_3229 : Litex.In _value_i2 (Litex.Z (M := M)) := h_3229
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3230)
                        have h_3230 : Litex.In _value_i3 (Litex.Z (M := M)) := h_3230
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3229) (Litex.integerToComplex _value_i3 h_3230))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3229) (Litex.integerToComplex _value_i3 h_3230))
                          exact (Litex.addInZ _value_i2 _value_i3 h_3229 h_3230))));
                      let _wd_2_1 := _value_i4;
                      let _wd_2_2 := _value_i5;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 h_2367 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_3396 h_3397 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3396)
                        have h_3396 : Litex.In _value_i2 (Litex.Z (M := M)) := h_3396
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3397)
                        have h_3397 : Litex.In _value_i3 (Litex.Z (M := M)) := h_3397
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3396) (Litex.integerToComplex _value_i3 h_3397))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3396) (Litex.integerToComplex _value_i3 h_3397))
                          exact (Litex.addInZ _value_i2 _value_i3 h_3396 h_3397))));
                      let _wd_2_1 := _value_i4;
                      let _wd_2_2 := _value_i5;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 h_2367 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_3646 h_3647 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3646)
              have h_3646 : Litex.In _value_i2 (Litex.Z (M := M)) := h_3646
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3647)
              have h_3647 : Litex.In _value_i3 (Litex.Z (M := M)) := h_3647
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3646) (Litex.integerToComplex _value_i3 h_3647))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3646) (Litex.integerToComplex _value_i3 h_3647))
                exact (Litex.addInZ _value_i2 _value_i3 h_3646 h_3647))));
            let _wd_2_1 := _value_i5;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2367 h_2368 True.intro))
            let _object_w13 := (Litex.add _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_2367) (Litex.integerToComplex _value_i6 h_2368))
            have h_2346 : (by
              let _equal_wd_2_0 := _object_w12
              let _equal_wd_2_1 := _object_w13
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_4513 h_4514 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4513)
                        have h_4513 : Litex.In _value_i2 (Litex.Z (M := M)) := h_4513
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4514)
                        have h_4514 : Litex.In _value_i3 (Litex.Z (M := M)) := h_4514
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4513) (Litex.integerToComplex _value_i3 h_4514))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4513) (Litex.integerToComplex _value_i3 h_4514))
                          exact (Litex.addInZ _value_i2 _value_i3 h_4513 h_4514))));
                      let _wd_2_1 := _value_i5;
                      let _wd_2_2 := _value_i6;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2367 h_2368 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_4684 h_4685 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4684)
                        have h_4684 : Litex.In _value_i2 (Litex.Z (M := M)) := h_4684
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4685)
                        have h_4685 : Litex.In _value_i3 (Litex.Z (M := M)) := h_4685
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4684) (Litex.integerToComplex _value_i3 h_4685))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4684) (Litex.integerToComplex _value_i3 h_4685))
                          exact (Litex.addInZ _value_i2 _value_i3 h_4684 h_4685))));
                      let _wd_2_1 := _value_i5;
                      let _wd_2_2 := _value_i6;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2367 h_2368 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_4938 h_4939 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4938)
              have h_4938 : Litex.In _value_i2 (Litex.Z (M := M)) := h_4938
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4939)
              have h_4939 : Litex.In _value_i3 (Litex.Z (M := M)) := h_4939
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4938) (Litex.integerToComplex _value_i3 h_4939))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4938) (Litex.integerToComplex _value_i3 h_4939))
                exact (Litex.addInZ _value_i2 _value_i3 h_4938 h_4939))));
            let _wd_2_1 := _object_w10;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w10
              exact (Litex.inOfSame _object_w10 _object_w10 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w10) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w10))) h_2368 True.intro))
            let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_5140 h_5141 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5140)
              have h_5140 : Litex.In _value_i2 (Litex.Z (M := M)) := h_5140
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5141)
              have h_5141 : Litex.In _value_i3 (Litex.Z (M := M)) := h_5141
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5140) (Litex.integerToComplex _value_i3 h_5141))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5140) (Litex.integerToComplex _value_i3 h_5141))
                exact (Litex.addInZ _value_i2 _value_i3 h_5140 h_5141))));
            let _wd_2_1 := _object_w11;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.addInZ _value_i4 _value_i5 h_2366 h_2367)) h_2368 True.intro))
            have h_2347 : (by
              let _equal_wd_2_0 := _object_w14
              let _equal_wd_2_1 := _object_w15
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_2345 (show @Eq M.Value _ _ from Eq.refl _)))
                  )
              )
            let _object_w16 := (let _wd_2_0 := _object_w11;
            let _wd_2_1 := _value_i6;
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.addInC _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_2366) (Litex.integerToComplex _value_i5 h_2367))) (Litex.integerToComplex _wd_2_1 h_2368)))
            have h_2348 : (by
              let _equal_wd_2_0 := _object_w15
              let _equal_wd_2_1 := _object_w16
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                      have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                      let _litex_original := _object_w15
                      let _litex_literal := _object_w15
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_5874 h_5875 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5874)
              have h_5874 : Litex.In _value_i2 (Litex.Z (M := M)) := h_5874
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5875)
              have h_5875 : Litex.In _value_i3 (Litex.Z (M := M)) := h_5875
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5874) (Litex.integerToComplex _value_i3 h_5875))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5874) (Litex.integerToComplex _value_i3 h_5875))
                exact (Litex.addInZ _value_i2 _value_i3 h_5874 h_5875))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _object_w12;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 (by
              let _atomic_wd_1_0 := _object_w12
              exact (Litex.inOfSame _object_w12 _object_w12 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w12) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w12))) True.intro))
            let _object_w18 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_6072 h_6073 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6072)
              have h_6072 : Litex.In _value_i2 (Litex.Z (M := M)) := h_6072
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6073)
              have h_6073 : Litex.In _value_i3 (Litex.Z (M := M)) := h_6073
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6072) (Litex.integerToComplex _value_i3 h_6073))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6072) (Litex.integerToComplex _value_i3 h_6073))
                exact (Litex.addInZ _value_i2 _value_i3 h_6072 h_6073))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _object_w13;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 (by
              let _atomic_wd_1_0 := _object_w13
              exact (Litex.addInZ _value_i5 _value_i6 h_2367 h_2368)) True.intro))
            have h_2349 : (by
              let _equal_wd_2_0 := _object_w17
              let _equal_wd_2_1 := _object_w18
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_2346))
                  )
              )
            let _object_w19 := (let _wd_2_0 := _value_i4;
            let _wd_2_1 := _object_w13;
            (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2366) (by
              let _atomic_wd_1_0 := _object_w13
              exact (Litex.addInC _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_2367) (Litex.integerToComplex _value_i6 h_2368)))))
            have h_2350 : (by
              let _equal_wd_2_0 := _object_w18
              let _equal_wd_2_1 := _object_w19
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) = (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                      let _litex_original := _object_w18
                      let _litex_literal := _object_w18
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            have h_2351 : (by
              let _equal_wd_2_0 := _object_w16
              let _equal_wd_2_1 := _object_w19
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i4 (Litex.integerToComplex _value_i4 h_2366)) + (Litex.NativeBridge.asComplex _value_i5 (Litex.integerToComplex _value_i5 h_2367))) + (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_2368))) ((Litex.NativeBridge.asComplex _value_i4 (Litex.integerToComplex _value_i4 h_2366)) + ((Litex.NativeBridge.asComplex _value_i5 (Litex.integerToComplex _value_i5 h_2367)) + (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_2368)))) (Litex.NativeBridge.denoteAdd (_object_w16).val.left _value_i6 (_object_w16).wd.1 (_object_w16).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i4 _value_i5 (_object_w11).wd.1 (_object_w11).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.integerToComplex _value_i4 h_2366)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.integerToComplex _value_i5 h_2367))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_2368))) (Litex.NativeBridge.denoteAdd _value_i4 (_object_w19).val.right (_object_w19).wd.1 (_object_w19).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.integerToComplex _value_i4 h_2366)) (Litex.NativeBridge.denoteAdd _value_i5 _value_i6 (_object_w13).wd.1 (_object_w13).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.integerToComplex _value_i5 h_2367)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_2368)))) (by ring!))
                  )
              )
            have h_2352 : (by
              let _equal_wd_2_0 := _object_w14
              let _equal_wd_2_1 := _object_w17
              exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    ((((((((h_2347).trans h_2348)).trans h_2351)).trans (h_2350).symm)).trans (h_2349).symm)
                  )
              )
            exact (And.intro h_2345 (And.intro h_2346 (And.intro h_2347 (And.intro h_2348 (And.intro h_2349 (And.intro h_2350 (And.intro h_2351 h_2352)))))))
          );
          let h_6796 : (by
            let _atomic_wd_1_0 := _wd_1_0
            exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M))))));
          Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_119 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_120 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) i).mpr ⟨h_6796 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_125 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_2353 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
          let _equal_wd_1_1 := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6811 h_6812 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6811)
            have h_6811 : Litex.In _value_i2 (Litex.Z (M := M)) := h_6811
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6812)
            have h_6812 : Litex.In _value_i3 (Litex.Z (M := M)) := h_6812
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6811) (Litex.integerToComplex _value_i3 h_6812))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6811) (Litex.integerToComplex _value_i3 h_6812))
              exact (Litex.addInZ _value_i2 _value_i3 h_6811 h_6812))));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _object_w22 := (let _wd_2_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_6907 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_6907)
            have h_6907 : Litex.In _value_i1 (Litex.Z (M := M)) := h_6907
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_6907));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _object_w22 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (by
            let _atomic_wd_1_0 := _object_w22
            exact (Litex.inOfSame _object_w22 _object_w22 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w22) (Litex.sameRefl (Litex.Z (M := M))) (Litex.callInOutput _object_w22))) True.intro))
          exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from by
          let _fold := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_17 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_17)
          have h_17 : Litex.In _value_i1 (Litex.Z (M := M)) := h_17
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_17));
        let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
          intro _raw_i2 _raw_i3 h_36 h_37 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_36)
          have h_36 : Litex.In _value_i2 (Litex.Z (M := M)) := h_36
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_37)
          have h_37 : Litex.In _value_i3 (Litex.Z (M := M)) := h_37
          change (by
            let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_36) (Litex.integerToComplex _value_i3 h_37))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_36) (Litex.integerToComplex _value_i3 h_37))
            exact (Litex.addInZ _value_i2 _value_i3 h_36 h_37))));
        let _wd_1_3 := (Litex.number (M := M) (0 : ℂ));
        (let h_119 : (by
          let _atomic_wd_1_0 := _wd_1_0
          exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0));
        let h_120 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
        let h_125 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_138 : Litex.In _value_i4 (Litex.Z (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_139 : Litex.In _value_i5 (Litex.Z (M := M))), (by
          let _object_w5 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_153 h_154 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_153)
            have h_153 : Litex.In _value_i2 (Litex.Z (M := M)) := h_153
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_154)
            have h_154 : Litex.In _value_i3 (Litex.Z (M := M)) := h_154
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_153) (Litex.integerToComplex _value_i3 h_154))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_153) (Litex.integerToComplex _value_i3 h_154))
              exact (Litex.addInZ _value_i2 _value_i3 h_153 h_154))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_138 h_139 True.intro))
          let _object_w6 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_138) (Litex.integerToComplex _value_i5 h_139))
          let _object_w7 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_1253 h_1254 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1253)
            have h_1253 : Litex.In _value_i2 (Litex.Z (M := M)) := h_1253
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1254)
            have h_1254 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1254
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1253) (Litex.integerToComplex _value_i3 h_1254))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1253) (Litex.integerToComplex _value_i3 h_1254))
              exact (Litex.addInZ _value_i2 _value_i3 h_1253 h_1254))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i4;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_138 True.intro))
          let _object_w8 := (Litex.add _value_i5 _value_i4 (Litex.integerToComplex _value_i5 h_139) (Litex.integerToComplex _value_i4 h_138))
          exact (((by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w7
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
        ) := (by
          intro _Host_i4 _rep_i4 _value_i4 h_138 _Host_i5 _rep_i5 _value_i5 h_139
          let _object_w5 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_153 h_154 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_153)
            have h_153 : Litex.In _value_i2 (Litex.Z (M := M)) := h_153
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_154)
            have h_154 : Litex.In _value_i3 (Litex.Z (M := M)) := h_154
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_153) (Litex.integerToComplex _value_i3 h_154))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_153) (Litex.integerToComplex _value_i3 h_154))
              exact (Litex.addInZ _value_i2 _value_i3 h_153 h_154))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_138 h_139 True.intro))
          let _object_w6 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_138) (Litex.integerToComplex _value_i5 h_139))
          have h_121 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_892 h_893 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_892)
                      have h_892 : Litex.In _value_i2 (Litex.Z (M := M)) := h_892
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_893)
                      have h_893 : Litex.In _value_i3 (Litex.Z (M := M)) := h_893
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_892) (Litex.integerToComplex _value_i3 h_893))
                        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_892) (Litex.integerToComplex _value_i3 h_893))
                        exact (Litex.addInZ _value_i2 _value_i3 h_892 h_893))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_138 h_139 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_1039 h_1040 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1039)
                      have h_1039 : Litex.In _value_i2 (Litex.Z (M := M)) := h_1039
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1040)
                      have h_1040 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1040
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1039) (Litex.integerToComplex _value_i3 h_1040))
                        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1039) (Litex.integerToComplex _value_i3 h_1040))
                        exact (Litex.addInZ _value_i2 _value_i3 h_1039 h_1040))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_138 h_139 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w7 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_1253 h_1254 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1253)
            have h_1253 : Litex.In _value_i2 (Litex.Z (M := M)) := h_1253
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1254)
            have h_1254 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1254
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1253) (Litex.integerToComplex _value_i3 h_1254))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1253) (Litex.integerToComplex _value_i3 h_1254))
              exact (Litex.addInZ _value_i2 _value_i3 h_1253 h_1254))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i4;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_138 True.intro))
          let _object_w8 := (Litex.add _value_i5 _value_i4 (Litex.integerToComplex _value_i5 h_139) (Litex.integerToComplex _value_i4 h_138))
          have h_122 : (by
            let _equal_wd_1_0 := _object_w7
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_1992 h_1993 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1992)
                      have h_1992 : Litex.In _value_i2 (Litex.Z (M := M)) := h_1992
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1993)
                      have h_1993 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1993
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1992) (Litex.integerToComplex _value_i3 h_1993))
                        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_1992) (Litex.integerToComplex _value_i3 h_1993))
                        exact (Litex.addInZ _value_i2 _value_i3 h_1992 h_1993))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i4;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_138 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_2139 h_2140 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2139)
                      have h_2139 : Litex.In _value_i2 (Litex.Z (M := M)) := h_2139
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2140)
                      have h_2140 : Litex.In _value_i3 (Litex.Z (M := M)) := h_2140
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2139) (Litex.integerToComplex _value_i3 h_2140))
                        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2139) (Litex.integerToComplex _value_i3 h_2140))
                        exact (Litex.addInZ _value_i2 _value_i3 h_2139 h_2140))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i4;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_138 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_123 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i4 (Litex.integerToComplex _value_i4 h_138)) + (Litex.NativeBridge.asComplex _value_i5 (Litex.integerToComplex _value_i5 h_139))) ((Litex.NativeBridge.asComplex _value_i5 (Litex.integerToComplex _value_i5 h_139)) + (Litex.NativeBridge.asComplex _value_i4 (Litex.integerToComplex _value_i4 h_138))) (Litex.NativeBridge.denoteAdd _value_i4 _value_i5 (_object_w6).wd.1 (_object_w6).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.integerToComplex _value_i4 h_138)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.integerToComplex _value_i5 h_139))) (Litex.NativeBridge.denoteAdd _value_i5 _value_i4 (_object_w8).wd.1 (_object_w8).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.integerToComplex _value_i5 h_139)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.integerToComplex _value_i4 h_138))) (by ring!))
                )
            )
          have h_124 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_121).trans h_123)).trans (h_122).symm)
                )
            )
          exact (And.intro h_121 (And.intro h_122 (And.intro h_123 h_124)))
        );
        let h_2353 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_2366 : Litex.In _value_i4 (Litex.Z (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_2367 : Litex.In _value_i5 (Litex.Z (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_2368 : Litex.In _value_i6 (Litex.Z (M := M))), (by
          let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_2382 h_2383 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2382)
            have h_2382 : Litex.In _value_i2 (Litex.Z (M := M)) := h_2382
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2383)
            have h_2383 : Litex.In _value_i3 (Litex.Z (M := M)) := h_2383
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2382) (Litex.integerToComplex _value_i3 h_2383))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2382) (Litex.integerToComplex _value_i3 h_2383))
              exact (Litex.addInZ _value_i2 _value_i3 h_2382 h_2383))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 h_2367 True.intro))
          let _object_w11 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_2366) (Litex.integerToComplex _value_i5 h_2367))
          let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_3646 h_3647 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3646)
            have h_3646 : Litex.In _value_i2 (Litex.Z (M := M)) := h_3646
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3647)
            have h_3647 : Litex.In _value_i3 (Litex.Z (M := M)) := h_3647
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3646) (Litex.integerToComplex _value_i3 h_3647))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3646) (Litex.integerToComplex _value_i3 h_3647))
              exact (Litex.addInZ _value_i2 _value_i3 h_3646 h_3647))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2367 h_2368 True.intro))
          let _object_w13 := (Litex.add _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_2367) (Litex.integerToComplex _value_i6 h_2368))
          let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_4938 h_4939 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4938)
            have h_4938 : Litex.In _value_i2 (Litex.Z (M := M)) := h_4938
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4939)
            have h_4939 : Litex.In _value_i3 (Litex.Z (M := M)) := h_4939
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4938) (Litex.integerToComplex _value_i3 h_4939))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4938) (Litex.integerToComplex _value_i3 h_4939))
              exact (Litex.addInZ _value_i2 _value_i3 h_4938 h_4939))));
          let _wd_2_1 := _object_w10;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.inOfSame _object_w10 _object_w10 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w10) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w10))) h_2368 True.intro))
          let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_5140 h_5141 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5140)
            have h_5140 : Litex.In _value_i2 (Litex.Z (M := M)) := h_5140
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5141)
            have h_5141 : Litex.In _value_i3 (Litex.Z (M := M)) := h_5141
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5140) (Litex.integerToComplex _value_i3 h_5141))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5140) (Litex.integerToComplex _value_i3 h_5141))
              exact (Litex.addInZ _value_i2 _value_i3 h_5140 h_5141))));
          let _wd_2_1 := _object_w11;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.addInZ _value_i4 _value_i5 h_2366 h_2367)) h_2368 True.intro))
          let _object_w16 := (let _wd_2_0 := _object_w11;
          let _wd_2_1 := _value_i6;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.addInC _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_2366) (Litex.integerToComplex _value_i5 h_2367))) (Litex.integerToComplex _wd_2_1 h_2368)))
          let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_5874 h_5875 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5874)
            have h_5874 : Litex.In _value_i2 (Litex.Z (M := M)) := h_5874
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5875)
            have h_5875 : Litex.In _value_i3 (Litex.Z (M := M)) := h_5875
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5874) (Litex.integerToComplex _value_i3 h_5875))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5874) (Litex.integerToComplex _value_i3 h_5875))
              exact (Litex.addInZ _value_i2 _value_i3 h_5874 h_5875))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w12;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.inOfSame _object_w12 _object_w12 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w12) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w12))) True.intro))
          let _object_w18 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6072 h_6073 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6072)
            have h_6072 : Litex.In _value_i2 (Litex.Z (M := M)) := h_6072
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6073)
            have h_6073 : Litex.In _value_i3 (Litex.Z (M := M)) := h_6073
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6072) (Litex.integerToComplex _value_i3 h_6073))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6072) (Litex.integerToComplex _value_i3 h_6073))
              exact (Litex.addInZ _value_i2 _value_i3 h_6072 h_6073))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w13;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 (by
            let _atomic_wd_1_0 := _object_w13
            exact (Litex.addInZ _value_i5 _value_i6 h_2367 h_2368)) True.intro))
          let _object_w19 := (let _wd_2_0 := _value_i4;
          let _wd_2_1 := _object_w13;
          (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2366) (by
            let _atomic_wd_1_0 := _object_w13
            exact (Litex.addInC _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_2367) (Litex.integerToComplex _value_i6 h_2368)))))
          exact (((by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w18
            let _equal_wd_1_1 := _object_w19
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w19
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w17
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
        ) := (by
          intro _Host_i4 _rep_i4 _value_i4 h_2366 _Host_i5 _rep_i5 _value_i5 h_2367 _Host_i6 _rep_i6 _value_i6 h_2368
          let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_2382 h_2383 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2382)
            have h_2382 : Litex.In _value_i2 (Litex.Z (M := M)) := h_2382
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2383)
            have h_2383 : Litex.In _value_i3 (Litex.Z (M := M)) := h_2383
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2382) (Litex.integerToComplex _value_i3 h_2383))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_2382) (Litex.integerToComplex _value_i3 h_2383))
              exact (Litex.addInZ _value_i2 _value_i3 h_2382 h_2383))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 h_2367 True.intro))
          let _object_w11 := (Litex.add _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_2366) (Litex.integerToComplex _value_i5 h_2367))
          have h_2345 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_3229 h_3230 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3229)
                      have h_3229 : Litex.In _value_i2 (Litex.Z (M := M)) := h_3229
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3230)
                      have h_3230 : Litex.In _value_i3 (Litex.Z (M := M)) := h_3230
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3229) (Litex.integerToComplex _value_i3 h_3230))
                        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3229) (Litex.integerToComplex _value_i3 h_3230))
                        exact (Litex.addInZ _value_i2 _value_i3 h_3229 h_3230))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 h_2367 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_3396 h_3397 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3396)
                      have h_3396 : Litex.In _value_i2 (Litex.Z (M := M)) := h_3396
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3397)
                      have h_3397 : Litex.In _value_i3 (Litex.Z (M := M)) := h_3397
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3396) (Litex.integerToComplex _value_i3 h_3397))
                        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3396) (Litex.integerToComplex _value_i3 h_3397))
                        exact (Litex.addInZ _value_i2 _value_i3 h_3396 h_3397))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 h_2367 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_3646 h_3647 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3646)
            have h_3646 : Litex.In _value_i2 (Litex.Z (M := M)) := h_3646
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3647)
            have h_3647 : Litex.In _value_i3 (Litex.Z (M := M)) := h_3647
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3646) (Litex.integerToComplex _value_i3 h_3647))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_3646) (Litex.integerToComplex _value_i3 h_3647))
              exact (Litex.addInZ _value_i2 _value_i3 h_3646 h_3647))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2367 h_2368 True.intro))
          let _object_w13 := (Litex.add _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_2367) (Litex.integerToComplex _value_i6 h_2368))
          have h_2346 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_4513 h_4514 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4513)
                      have h_4513 : Litex.In _value_i2 (Litex.Z (M := M)) := h_4513
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4514)
                      have h_4514 : Litex.In _value_i3 (Litex.Z (M := M)) := h_4514
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4513) (Litex.integerToComplex _value_i3 h_4514))
                        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4513) (Litex.integerToComplex _value_i3 h_4514))
                        exact (Litex.addInZ _value_i2 _value_i3 h_4513 h_4514))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i6;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2367 h_2368 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_4684 h_4685 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4684)
                      have h_4684 : Litex.In _value_i2 (Litex.Z (M := M)) := h_4684
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4685)
                      have h_4685 : Litex.In _value_i3 (Litex.Z (M := M)) := h_4685
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4684) (Litex.integerToComplex _value_i3 h_4685))
                        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4684) (Litex.integerToComplex _value_i3 h_4685))
                        exact (Litex.addInZ _value_i2 _value_i3 h_4684 h_4685))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i6;
                    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2367 h_2368 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_4938 h_4939 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4938)
            have h_4938 : Litex.In _value_i2 (Litex.Z (M := M)) := h_4938
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4939)
            have h_4939 : Litex.In _value_i3 (Litex.Z (M := M)) := h_4939
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4938) (Litex.integerToComplex _value_i3 h_4939))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_4938) (Litex.integerToComplex _value_i3 h_4939))
              exact (Litex.addInZ _value_i2 _value_i3 h_4938 h_4939))));
          let _wd_2_1 := _object_w10;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.inOfSame _object_w10 _object_w10 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w10) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w10))) h_2368 True.intro))
          let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_5140 h_5141 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5140)
            have h_5140 : Litex.In _value_i2 (Litex.Z (M := M)) := h_5140
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5141)
            have h_5141 : Litex.In _value_i3 (Litex.Z (M := M)) := h_5141
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5140) (Litex.integerToComplex _value_i3 h_5141))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5140) (Litex.integerToComplex _value_i3 h_5141))
              exact (Litex.addInZ _value_i2 _value_i3 h_5140 h_5141))));
          let _wd_2_1 := _object_w11;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.addInZ _value_i4 _value_i5 h_2366 h_2367)) h_2368 True.intro))
          have h_2347 : (by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_2345 (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w16 := (let _wd_2_0 := _object_w11;
          let _wd_2_1 := _value_i6;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.addInC _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_2366) (Litex.integerToComplex _value_i5 h_2367))) (Litex.integerToComplex _wd_2_1 h_2368)))
          have h_2348 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                    let _litex_original := _object_w15
                    let _litex_literal := _object_w15
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_5874 h_5875 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5874)
            have h_5874 : Litex.In _value_i2 (Litex.Z (M := M)) := h_5874
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5875)
            have h_5875 : Litex.In _value_i3 (Litex.Z (M := M)) := h_5875
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5874) (Litex.integerToComplex _value_i3 h_5875))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_5874) (Litex.integerToComplex _value_i3 h_5875))
              exact (Litex.addInZ _value_i2 _value_i3 h_5874 h_5875))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w12;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.inOfSame _object_w12 _object_w12 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w12) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w12))) True.intro))
          let _object_w18 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6072 h_6073 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6072)
            have h_6072 : Litex.In _value_i2 (Litex.Z (M := M)) := h_6072
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6073)
            have h_6073 : Litex.In _value_i3 (Litex.Z (M := M)) := h_6073
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6072) (Litex.integerToComplex _value_i3 h_6073))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_6072) (Litex.integerToComplex _value_i3 h_6073))
              exact (Litex.addInZ _value_i2 _value_i3 h_6072 h_6073))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w13;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2366 (by
            let _atomic_wd_1_0 := _object_w13
            exact (Litex.addInZ _value_i5 _value_i6 h_2367 h_2368)) True.intro))
          have h_2349 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_2346))
                )
            )
          let _object_w19 := (let _wd_2_0 := _value_i4;
          let _wd_2_1 := _object_w13;
          (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2366) (by
            let _atomic_wd_1_0 := _object_w13
            exact (Litex.addInC _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_2367) (Litex.integerToComplex _value_i6 h_2368)))))
          have h_2350 : (by
            let _equal_wd_1_0 := _object_w18
            let _equal_wd_1_1 := _object_w19
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) = (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                    let _litex_original := _object_w18
                    let _litex_literal := _object_w18
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i4) (M.addValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_2351 : (by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w19
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i4 (Litex.integerToComplex _value_i4 h_2366)) + (Litex.NativeBridge.asComplex _value_i5 (Litex.integerToComplex _value_i5 h_2367))) + (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_2368))) ((Litex.NativeBridge.asComplex _value_i4 (Litex.integerToComplex _value_i4 h_2366)) + ((Litex.NativeBridge.asComplex _value_i5 (Litex.integerToComplex _value_i5 h_2367)) + (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 h_2368)))) (Litex.NativeBridge.denoteAdd (_object_w16).val.left _value_i6 (_object_w16).wd.1 (_object_w16).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i4 _value_i5 (_object_w11).wd.1 (_object_w11).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.integerToComplex _value_i4 h_2366)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.integerToComplex _value_i5 h_2367))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_2368))) (Litex.NativeBridge.denoteAdd _value_i4 (_object_w19).val.right (_object_w19).wd.1 (_object_w19).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.integerToComplex _value_i4 h_2366)) (Litex.NativeBridge.denoteAdd _value_i5 _value_i6 (_object_w13).wd.1 (_object_w13).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.integerToComplex _value_i5 h_2367)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 h_2368)))) (by ring!))
                )
            )
          have h_2352 : (by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w17
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((((((h_2347).trans h_2348)).trans h_2351)).trans (h_2350).symm)).trans (h_2349).symm)
                )
            )
          exact (And.intro h_2345 (And.intro h_2346 (And.intro h_2347 (And.intro h_2348 (And.intro h_2349 (And.intro h_2350 (And.intro h_2351 h_2352)))))))
        );
        let h_6796 : (by
          let _atomic_wd_1_0 := _wd_1_0
          exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M))))));
        Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_119 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_120 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) i).mpr ⟨h_6796 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_125 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_2353 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
          let _element := (Litex.number (M := M) (2 : ℂ))
          let _singleton := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)
          have _set_same : Litex.denote _fold.val.set = Litex.denote _singleton := h_1
          apply Litex.finiteFoldSingleton _fold (Litex.denote _element)
          intro y
          rw [_set_same]
          exact (Litex.finiteMembersInsert _singleton (Litex.denote _element) [] rfl Litex.finiteMembersEmpty y).trans (by simp only [List.mem_singleton]))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_fold_x5f_singleton_x2f_statement_x2e_lit
