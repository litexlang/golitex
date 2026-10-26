import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_min_x5f_max_x5f_functions_x2f_statement_x2e_lit

universe u v7 v8 v10 v11 v13 v14
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (by
  intro _raw_i2 _raw_i3 h_14 h_15 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
  have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
  change (by
    let _atomic_wd_1_0 := (Litex.min _value_i2 _value_i3 h_14 h_15)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.min _value_i2 _value_i3 h_14 h_15)
    exact (by
      let _extremum := _atomic_wd_1_0
      exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
    ))))
theorem h_52 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_53 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (Litex.minMaxValue (M := M) true _raw_i5 _raw_i6)) (by
  intro _raw_i5 _raw_i6 h_67 h_68 _
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_67)
  have h_67 : Litex.In _value_i5 (Litex.R (M := M)) := h_67
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_68)
  have h_68 : Litex.In _value_i6 (Litex.R (M := M)) := h_68
  change (by
    let _atomic_wd_1_0 := (Litex.max _value_i5 _value_i6 h_67 h_68)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.max _value_i5 _value_i6 h_67 h_68)
    exact (by
      let _extremum := _atomic_wd_1_0
      exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
    ))))
theorem h_109 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_110 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

noncomputable def _object_w9 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (h_52 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro)

theorem h_111 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w9 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (3 : ℂ)), (M.number (5 : ℂ))])) = (M.number (3 : ℂ)) from by
          have _litex_residual : ((Litex.minMaxValue (M := M) false) (M.number (3 : ℂ)) (M.number (5 : ℂ))) = (M.number (3 : ℂ)) := (let _equal_wd_2_0 := (Litex.min (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (3 : ℂ) (let _extremum := _equal_wd_2_0;
          let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
          Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (3 : ℂ)), (M.number (5 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (3 : ℂ)), (M.number (5 : ℂ))])) = ((Litex.minMaxValue (M := M) false) (M.number (3 : ℂ)) (M.number (5 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (5 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_53 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = ((Litex.minMaxValue (M := M) false) (M.number (3 : ℂ)) (M.number (5 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w11 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (_object_i4 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (h_109 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro)

theorem h_184 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (3 : ℂ)), (M.number (5 : ℂ))])) = (M.number (5 : ℂ)) from by
          have _litex_residual : ((Litex.minMaxValue (M := M) true) (M.number (3 : ℂ)) (M.number (5 : ℂ))) = (M.number (5 : ℂ)) := (let _equal_wd_2_0 := (Litex.max (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (5 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (5 : ℂ)) ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (5 : ℂ) (let _extremum := _equal_wd_2_0;
          let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
          Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (3 : ℂ)), (M.number (5 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (3 : ℂ)), (M.number (5 : ℂ))])) = ((Litex.minMaxValue (M := M) true) (M.number (3 : ℂ)) (M.number (5 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (5 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_110 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (Litex.minMaxValue (M := M) true _raw_i5 _raw_i6)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (Litex.minMaxValue (M := M) true _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (Litex.minMaxValue (M := M) true _raw_i5 _raw_i6)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = ((Litex.minMaxValue (M := M) true) (M.number (3 : ℂ)) (M.number (5 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_259 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_262 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_263 : Litex.In _value_i8 (Litex.R (M := M))) (h_257 : Litex.Le _value_i7 _value_i8), (by
  let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) _value_i7 _value_i8 (h_52 (M := M)) h_262 h_263 True.intro)
  exact Litex.Same _equal_wd_1_0 _value_i7) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_262 _Host_i8 _rep_i8 _value_i8 h_263 h_257
          have h_348 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_262
                )
            )
          have h_349 : Litex.In _value_i8 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_263
                )
            )
          let _object_w15 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) _value_i7 _value_i8 (h_52 (M := M)) h_348 h_349 True.intro)

          let _object_w16 := (Litex.min _value_i7 _value_i8 h_348 h_349)

          have h_260 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w15;
                  let _equal_wd_1_1 := _object_w16;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = ((Litex.minMaxValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                    have _litex_residual : ((Litex.minMaxValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i8)) = ((Litex.minMaxValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = ((Litex.minMaxValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i7;
                    let _wd_1_2 := _value_i8;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_348 h_349 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_53 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = ((Litex.minMaxValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i8)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_261 : (by
            let _equal_wd_1_0 := _object_w16
            exact Litex.Same _equal_wd_1_0 _value_i7) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w16;
                  (show Litex.Same _equal_wd_1_0 _value_i7 from (Litex.minOfLeOperands _equal_wd_1_0 h_257)))
                )
            )
          exact ((h_260).trans h_261)
        )
      )
  )

def prop_6 {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) : Prop :=
  ∃ (h_2616 : Litex.In _value_i10 (Litex.R (M := M))), ∃ (h_2617 : Litex.In _value_i11 (Litex.R (M := M))), Litex.Le _value_i10 _value_i11

theorem h_2692 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_2696 : Litex.In _value_i13 (Litex.R (M := M))) {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_2697 : Litex.In _value_i14 (Litex.R (M := M))) (h_2690 : ((prop_6 (M := M)) _value_i13 _value_i14)), (by
  let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (_object_i4 (M := M)) _value_i13 _value_i14 (h_109 (M := M)) h_2696 h_2697 True.intro)
  exact Litex.Same _equal_wd_1_0 _value_i14) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 h_2696 _Host_i14 _rep_i14 _value_i14 h_2697 h_2690
          have h_2698 :=
            (Classical.choose (show ((prop_6 (M := M)) _value_i13 _value_i14) from h_2690))
          have h_2699 :=
            (Classical.choose (Classical.choose_spec (show ((prop_6 (M := M)) _value_i13 _value_i14) from h_2690)))
          have h_2700 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_6 (M := M)) _value_i13 _value_i14) from h_2690)))
          have h_2713 : Litex.In _value_i13 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_2696
                )
            )
          have h_2714 : Litex.In _value_i14 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_2697
                )
            )
          have h_2715 :=
            (Classical.choose (show ((prop_6 (M := M)) _value_i13 _value_i14) from h_2690))
          have h_2716 :=
            (Classical.choose (Classical.choose_spec (show ((prop_6 (M := M)) _value_i13 _value_i14) from h_2690)))
          have h_2717 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_6 (M := M)) _value_i13 _value_i14) from h_2690)))
          have h_2693 : Litex.Le _value_i13 _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  h_2717
                )
            )
          let _object_w21 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (_object_i4 (M := M)) _value_i13 _value_i14 (h_109 (M := M)) h_2713 h_2714 True.intro)

          let _object_w22 := (Litex.max _value_i13 _value_i14 h_2713 h_2714)

          have h_2694 : (by
            let _equal_wd_1_0 := _object_w21
            let _equal_wd_1_1 := _object_w22
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w21;
                  let _equal_wd_1_1 := _object_w22;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = ((Litex.minMaxValue (M := M) true) (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
                    have _litex_residual : ((Litex.minMaxValue (M := M) true) (Litex.denote _value_i13) (Litex.denote _value_i14)) = ((Litex.minMaxValue (M := M) true) (Litex.denote _value_i13) (Litex.denote _value_i14)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = ((Litex.minMaxValue (M := M) true) (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                    let _wd_1_1 := _value_i13;
                    let _wd_1_2 := _value_i14;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_2713 h_2714 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_110 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (Litex.minMaxValue (M := M) true _raw_i5 _raw_i6)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (Litex.minMaxValue (M := M) true _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (Litex.minMaxValue (M := M) true _raw_i5 _raw_i6)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = ((Litex.minMaxValue (M := M) true) (Litex.denote _value_i13) (Litex.denote _value_i14)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_2695 : (by
            let _equal_wd_1_0 := _object_w22
            exact Litex.Same _equal_wd_1_0 _value_i14) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w22;
                  (show Litex.Same _equal_wd_1_0 _value_i14 from (Litex.maxOfLeOperands _equal_wd_1_0 h_2717)))
                )
            )
          exact ((h_2694).trans h_2695)
        )
      )
  )

noncomputable def _object_i16 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (h_52 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) True.intro)
theorem h_5582 : Litex.Same (_object_i16 (M := M)) (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (h_52 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) True.intro) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (h_52 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) True.intro))
      )
  )

theorem h_5583 : (by
  let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (h_52 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_5584 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_5585 : Litex.In (Litex.number (M := M) (7 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))
                )
            )
          have h_5586 : Litex.Le (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) h_5584 h_5585).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) h_5584 = (2 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) h_5584).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (7 : ℂ)) h_5585 = (7 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (7 : ℂ)) h_5585).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                )
            )
          have h_5610 : Litex.In (Litex.number (M := M) (7 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_5584).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) h_5584 = (2 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) h_5584).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_5586)
                )
            )
          have h_5587 : Litex.Same (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (h_52 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) True.intro) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_259 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_5584 (Litex.number (M := M) (7 : ℂ)) h_5585 h_5586)
                )
            )
          exact (let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (h_52 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_5587).trans (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))))))
        )
      )
  )

theorem h_5639 : Litex.Same (_object_i16 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (((h_5582 (M := M))).trans (h_5583 (M := M)))
      )
  )

theorem h_5641 : ((prop_6 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Exists.intro (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Exists.intro (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) = (7 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
      )
  )

theorem h_5663 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_5641 (M := M)) with ⟨h_2616, h_2617, h_2615⟩; exact h_2616)
      )
  )

theorem h_5664 : Litex.In (Litex.number (M := M) (7 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_5641 (M := M)) with ⟨h_2616, h_2617, h_2615⟩; exact h_2617)
      )
  )

theorem h_5665 : Litex.Le (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_5641 (M := M)) with ⟨h_2616, h_2617, h_2615⟩; exact h_2615)
      )
  )

theorem h_5666 : (by
  have h_5667 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (h_5663 (M := M))
        )
    )
  have h_5668 : Litex.In (Litex.number (M := M) (7 : ℂ)) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (h_5664 (M := M))
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (_object_i4 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (h_109 (M := M)) h_5667 h_5668 True.intro)
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_5667 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_5663 (M := M))
                )
            )
          have h_5668 : Litex.In (Litex.number (M := M) (7 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_5664 (M := M))
                )
            )
          have h_5669 : ((prop_6 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_5641 (M := M))
                )
            )
          have h_5695 :=
            (Classical.choose (show ((prop_6 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ))) from h_5669))
          have h_5696 :=
            (Classical.choose (Classical.choose_spec (show ((prop_6 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ))) from h_5669)))
          have h_5697 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_6 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ))) from h_5669)))
          have h_5670 : Litex.Same (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (_object_i4 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (h_109 (M := M)) h_5667 h_5668 True.intro) (Litex.number (M := M) (7 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2692 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_5667 (Litex.number (M := M) (7 : ℂ)) h_5668 h_5669)
                )
            )
          exact (let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (_object_i4 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (h_109 (M := M)) h_5667 h_5668 True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_5670).trans (Litex.sameRefl (Litex.number (M := M) (7 : ℂ)))))))
        )
      )
  )

noncomputable def _object_i17 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.minMaxValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i18, (M.number (5 : ℂ))])) (M.number (0 : ℂ)))) (by
  intro _raw_i18 h_5744 _
  let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_5744)
  have h_5744 : Litex.In _value_i18 (Litex.R (M := M)) := h_5744
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) _value_i18 (Litex.number (M := M) (5 : ℂ)) (h_52 (M := M)) h_5744 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro);
    let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
    (Litex.max _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) _value_i18 (Litex.number (M := M) (5 : ℂ)) (h_52 (M := M)) h_5744 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro);
    let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
    (Litex.max _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))
    exact (by
      let _extremum := _atomic_wd_1_0
      exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
    ))))
theorem h_6068 : Litex.In (_object_i17 (M := M)) (Litex.fnSet ((_object_i17 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i17 (M := M)))
      )
  )
theorem h_6069 : Litex.Same (_object_i17 (M := M)) (_object_i17 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i17 (M := M)))
      )
  )

noncomputable def _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (_object_i17 (M := M)) (Litex.number (M := M) (7 : ℂ)) (h_6068 (M := M)) (h_5664 (M := M)) True.intro)

theorem h_6070 : (by
  let _equal_wd_1_0 := (_object_w36 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w36 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (M.number (7 : ℂ))) = (M.number (5 : ℂ)) from by
          have _litex_residual : ((Litex.minMaxValue (M := M) true) ((Litex.minMaxValue (M := M) false) (M.number (7 : ℂ)) (M.number (5 : ℂ))) (M.number (0 : ℂ))) = (M.number (5 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.min (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (h_5664 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.max _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((Min.min (7 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := _atomic_wd_1_0;
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (7 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (((7 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Min.min (7 : ℝ) (5 : ℝ) : ℝ) : ℂ) (5 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (5 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (5 : ℂ)) ((Max.max (5 : ℝ) (0 : ℝ) : ℝ) : ℂ) (5 : ℂ) (let _extremum := _equal_wd_2_0;
          let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
          Litex.minMaxDenoteReal _extremum (5 : ℝ) (0 : ℝ) (((let _extremum := (_equal_wd_2_0).val.left;
          let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
          Litex.minMaxDenoteReal _extremum (7 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (((7 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ)))))).trans (congrArg M.number (by norm_num : ((Min.min (7 : ℝ) (5 : ℝ) : ℝ) : ℂ) = (((5 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num))))
          exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (M.number (7 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (M.number (7 : ℂ))) = ((Litex.minMaxValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (7 : ℂ)), (M.number (5 : ℂ))])) (M.number (0 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i17 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (7 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (h_5664 (M := M)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_6069 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.minMaxValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i18, (M.number (5 : ℂ))])) (M.number (0 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i18 : M.Value) => (Litex.minMaxValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i18, (M.number (5 : ℂ))])) (M.number (0 : ℂ)))) (Litex.denote _litex_literal.val.argument) = ((Litex.minMaxValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (7 : ℂ)), (M.number (5 : ℂ))])) (M.number (0 : ℂ))) from rfl))
        ))).trans (congrArg₂ (Litex.minMaxValue (M := M) true) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (7 : ℂ)), (M.number (5 : ℂ))])) = ((Litex.minMaxValue (M := M) false) (M.number (7 : ℂ)) (M.number (5 : ℂ))) from by
          let _litex_original := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (h_52 (M := M)) (h_5664 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro)
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (7 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (5 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (h_5664 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_53 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = ((Litex.minMaxValue (M := M) false) (M.number (7 : ℂ)) (M.number (5 : ℂ))) from rfl))
        ) rfl))).trans _litex_residual)))
      )
  )

noncomputable def _object_w44 := (let _object_w37 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (_object_i17 (M := M)) _object_w37 (h_6068 (M := M)) (by
  let _atomic_wd_1_0 := _object_w37
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w37).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) True.intro))

theorem h_6298 : (by
  let _equal_wd_1_0 := (_object_w44 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w44 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (M.negValue (M.number (2 : ℂ)))) = (M.number (0 : ℂ)) from by
          have _litex_residual : ((Litex.minMaxValue (M := M) true) ((Litex.minMaxValue (M := M) false) (M.negValue (M.number (2 : ℂ))) (M.number (5 : ℂ))) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (_equal_wd_1_0).val.argument;
          let _wd_2_1 := (Litex.number (M := M) (5 : ℂ));
          (Litex.min _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.max _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((Min.min (-2 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := _atomic_wd_1_0;
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (-2 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (((-2 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Min.min (-2 : ℝ) (5 : ℝ) : ℝ) : ℂ) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) ((Max.max (-2 : ℝ) (0 : ℝ) : ℝ) : ℂ) (0 : ℂ) (let _extremum := _equal_wd_2_0;
          let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
          Litex.minMaxDenoteReal _extremum (-2 : ℝ) (0 : ℝ) (((let _extremum := (_equal_wd_2_0).val.left;
          let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
          Litex.minMaxDenoteReal _extremum (-2 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (((_equal_wd_2_0).val.left).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (((-2 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ)))))).trans (congrArg M.number (by norm_num : ((Min.min (-2 : ℝ) (5 : ℝ) : ℝ) : ℂ) = (((-2 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (M.negValue (M.number (2 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (M.negValue (M.number (2 : ℂ)))) = ((Litex.minMaxValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (2 : ℂ))), (M.number (5 : ℂ))])) (M.number (0 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i17 (M := M));
          let _object_w41 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) _wd_1_0 _object_w41 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w41
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w41).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_6069 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.minMaxValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i18, (M.number (5 : ℂ))])) (M.number (0 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i18 : M.Value) => (Litex.minMaxValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i18, (M.number (5 : ℂ))])) (M.number (0 : ℂ)))) (Litex.denote _litex_literal.val.argument) = ((Litex.minMaxValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (2 : ℂ))), (M.number (5 : ℂ))])) (M.number (0 : ℂ))) from rfl))
        ))).trans (congrArg₂ (Litex.minMaxValue (M := M) true) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (2 : ℂ))), (M.number (5 : ℂ))])) = ((Litex.minMaxValue (M := M) false) (M.negValue (M.number (2 : ℂ))) (M.number (5 : ℂ))) from by
          let _litex_original := (let _object_w42 := (_equal_wd_1_0).val.argument;
          let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) _object_w42 _wd_1_1 (h_52 (M := M)) (by
            let _atomic_wd_1_0 := _object_w42
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w42).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro))
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _object_w43 := (_equal_wd_1_0).val.argument;
          let _wd_1_2 := (Litex.number (M := M) (5 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _object_w43 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w43
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w43).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_53 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.minMaxValue (M := M) false _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = ((Litex.minMaxValue (M := M) false) (M.negValue (M.number (2 : ℂ))) (M.number (5 : ℂ))) from rfl))
        ) rfl))).trans _litex_residual)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_min_x5f_max_x5f_functions_x2f_statement_x2e_lit
