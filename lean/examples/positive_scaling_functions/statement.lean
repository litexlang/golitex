import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_scaling_x5f_functions_x2f_statement_x2e_lit

universe u v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn2Target (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
  rintro _raw_i2 _raw_i3 h_27 h_31 ⟨_positive_i2, _positive_i3⟩
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27)
  have h_27 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_27, _positive_i2⟩)
  have h_28 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i2 h_27)
        )
    )
  have h_29 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_28)
        )
    )
  have h_30 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_28) _litex_zero.symm)
        )
    )
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_31)
  have h_31 : Litex.In _value_i3 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i3).mpr ⟨h_31, _positive_i3⟩)
  have h_32 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i3 h_31)
        )
    )
  have h_33 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_32)
        )
    )
  have h_34 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_32) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.positiveRealToComplex _value_i2 h_27) (Litex.positiveRealToComplex _value_i3 h_31))
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.positiveRealToComplex _value_i2 h_27) (Litex.positiveRealToComplex _value_i3 h_31))
    exact (Litex.mulInRPos _atomic_wd_1_0 h_27 h_31))))
theorem h_157 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_158 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn2Target (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i5)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i6)))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.divValue _raw_i5 _raw_i6)) (by
  rintro _raw_i5 _raw_i6 h_185 h_189 ⟨_positive_i5, _positive_i6⟩
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_185)
  have h_185 : Litex.In _value_i5 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i5).mpr ⟨h_185, _positive_i5⟩)
  have h_186 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i5 h_185)
        )
    )
  have h_187 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_186)
        )
    )
  have h_188 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_186) _litex_zero.symm)
        )
    )
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_189)
  have h_189 : Litex.In _value_i6 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i6).mpr ⟨h_189, _positive_i6⟩)
  have h_190 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i6 h_189)
        )
    )
  have h_191 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_190)
        )
    )
  have h_192 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_190) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i5 _value_i6 (Litex.positiveRealToComplex _value_i5 h_185) (Litex.positiveRealToComplex _value_i6 h_189) h_192)
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i5 _value_i6 (Litex.positiveRealToComplex _value_i5 h_185) (Litex.positiveRealToComplex _value_i6 h_189) h_192)
    exact (Litex.divInRPos _atomic_wd_1_0 h_185 h_189))))
theorem h_353 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_354 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

theorem h_356 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_381 : Litex.In _value_i7 (Litex.RPos (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_385 : Litex.In _value_i8 (Litex.RPos (M := M))), (by
  let _object_w20 := (let _object_w15 := (Litex.call2Target Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) (_object_i1 (M := M)) _value_i7 _value_i8 (h_157 (M := M)) (Litex.inRPos_real _value_i7 h_381) (Litex.inRPos_real _value_i8 h_385) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote _value_i7)).mp h_381).2 ((Litex.positiveReal_members (M := M) (Litex.denote _value_i8)).mp h_385).2));
  let _wd_1_1 := _value_i8;
  (Litex.call2Target Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i5)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i6)))) (_object_i4 (M := M)) _object_w15 _wd_1_1 (h_353 (M := M)) (Litex.inRPos_real _object_w15 (by
    let _atomic_wd_1_0 := _object_w15
    exact (by
      let _litex_return_call := _object_w15
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.call2InOutput _litex_return_call)))) (Litex.inRPos_real _wd_1_1 h_385) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote _object_w15)).mp (by
    let _atomic_wd_1_0 := _object_w15
    exact (by
      let _litex_return_call := _object_w15
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.call2InOutput _litex_return_call)))).2 ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_385).2)))
  exact (by
    let _equal_wd_1_0 := _object_w20
    exact Litex.Same _equal_wd_1_0 _value_i7)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_381 _Host_i8 _rep_i8 _value_i8 h_385
          have h_382 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i7 h_381)
                )
            )
          have h_383 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_382)
                )
            )
          have h_384 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_382) _litex_zero.symm)
                )
            )
          have h_386 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i8 h_385)
                )
            )
          have h_387 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i8 h_386)
                )
            )
          have h_388 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i8 h_386) _litex_zero.symm)
                )
            )
          let _object_w20 := (let _object_w15 := (Litex.call2Target Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) (_object_i1 (M := M)) _value_i7 _value_i8 (h_157 (M := M)) (Litex.inRPos_real _value_i7 h_381) (Litex.inRPos_real _value_i8 h_385) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote _value_i7)).mp h_381).2 ((Litex.positiveReal_members (M := M) (Litex.denote _value_i8)).mp h_385).2));
          let _wd_1_1 := _value_i8;
          (Litex.call2Target Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i5)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i6)))) (_object_i4 (M := M)) _object_w15 _wd_1_1 (h_353 (M := M)) (Litex.inRPos_real _object_w15 (by
            let _atomic_wd_1_0 := _object_w15
            exact (by
              let _litex_return_call := _object_w15
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.call2InOutput _litex_return_call)))) (Litex.inRPos_real _wd_1_1 h_385) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote _object_w15)).mp (by
            let _atomic_wd_1_0 := _object_w15
            exact (by
              let _litex_return_call := _object_w15
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.call2InOutput _litex_return_call)))).2 ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_385).2)))
          have h_355 : (by
            let _equal_wd_1_0 := _object_w20
            exact Litex.Same _equal_wd_1_0 _value_i7) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w20;
                  (show Litex.Same _equal_wd_1_0 _value_i7 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])), (Litex.denote _value_i8)])) = (Litex.denote _value_i7) from by
                    have _litex_residual : (M.divValue (M.mulValue (Litex.denote _value_i7) (Litex.denote _value_i8)) (Litex.denote _value_i8)) = (Litex.denote _value_i7) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.mul _value_i7 _value_i8 (Litex.positiveRealToComplex _value_i7 h_381) (Litex.positiveRealToComplex _value_i8 h_385));
                    let _wd_1_1 := _value_i8;
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i7 _wd_1_1 (Litex.positiveRealToComplex _value_i7 h_381) (Litex.positiveRealToComplex _wd_1_1 h_385))) (Litex.positiveRealToComplex _wd_1_1 h_385) h_388));
                    (show Litex.Same _equal_wd_2_0 _value_i7 from (by
                      let _quotient := _equal_wd_2_0
                      let _product := (_equal_wd_2_0).val.left
                      have _child : (by
                        let _equal_wd_3_0 := (_equal_wd_2_0).val.left
                        let _equal_wd_3_1 := _equal_wd_3_0
                        exact Litex.Same _equal_wd_3_1 _equal_wd_3_1) := (show @Eq M.Value _ _ from Eq.refl _)
                      have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.left _quotient.wd.1 _quotient.wd.2.1 _product.wd.1 _quotient.wd.2.2
                      exact (_conversion.mpr _child))))
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])), (Litex.denote _value_i8)])))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_x, (Litex.denote _value_i8)])) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.mulValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                    let _litex_original := (_equal_wd_1_0).val.first
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i7;
                    let _wd_1_2 := _value_i8;
                    (Litex.call2Target Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_381) (Litex.inRPos_real _wd_1_2 h_385) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_381).2 ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_2)).mp h_385).2)))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_158 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2Target_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.twoTarget_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (Litex.denote (Litex.RPos (M := M))) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from rfl))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i7) (Litex.denote _value_i8)), (Litex.denote _value_i8)])) = (M.divValue (M.mulValue (Litex.denote _value_i7) (Litex.denote _value_i8)) (Litex.denote _value_i8)) from by
                    let _litex_original := (let _object_w18 := (Litex.mul _value_i7 _value_i8 (Litex.positiveRealToComplex _value_i7 h_381) (Litex.positiveRealToComplex _value_i8 h_385));
                    let _wd_1_1 := _value_i8;
                    (Litex.call2Target Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i5)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i6)))) (_object_i4 (M := M)) _object_w18 _wd_1_1 (h_353 (M := M)) (Litex.inRPos_real _object_w18 (by
                      let _atomic_wd_1_0 := _object_w18
                      exact (Litex.mulInRPos _atomic_wd_1_0 h_381 h_385))) (Litex.inRPos_real _wd_1_1 h_385) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote _object_w18)).mp (by
                      let _atomic_wd_1_0 := _object_w18
                      exact (Litex.mulInRPos _atomic_wd_1_0 h_381 h_385))).2 ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_385).2)))
                    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                    let _object_w19 := (Litex.mul _value_i7 _value_i8 (Litex.positiveRealToComplex _value_i7 h_381) (Litex.positiveRealToComplex _value_i8 h_385));
                    let _wd_1_2 := _value_i8;
                    (Litex.call2Target Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i5)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i6)))) _wd_1_0 _object_w19 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _object_w19 (by
                      let _atomic_wd_1_0 := _object_w19
                      exact (Litex.mulInRPos _atomic_wd_1_0 h_381 h_385))) (Litex.inRPos_real _wd_1_2 h_385) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote _object_w19)).mp (by
                      let _atomic_wd_1_0 := _object_w19
                      exact (Litex.mulInRPos _atomic_wd_1_0 h_381 h_385))).2 ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_2)).mp h_385).2)))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_354 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2Target_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i5)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i6)))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.divValue _raw_i5 _raw_i6)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.twoTarget_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i5)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i6)))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.divValue _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (Litex.denote (Litex.RPos (M := M))) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.divValue _raw_i5 _raw_i6)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.mulValue (Litex.denote _value_i7) (Litex.denote _value_i8)) (Litex.denote _value_i8)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_355
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_scaling_x5f_functions_x2f_statement_x2e_lit
