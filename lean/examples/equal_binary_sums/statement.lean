import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_binary_x5f_sums_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
  intro _raw_i2 _raw_i3 h_14 h_15 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
  have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (M.real_subset_complex _ h_14) (M.real_subset_complex _ h_15))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (M.real_subset_complex _ h_14) (M.real_subset_complex _ h_15))
    exact (Litex.addInR _value_i2 _value_i3 h_14 h_15))))
theorem h_89 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_90 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue _raw_i6 _raw_i5)) (by
  intro _raw_i5 _raw_i6 h_104 h_105 _
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_104)
  have h_104 : Litex.In _value_i5 (Litex.R (M := M)) := h_104
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_105)
  have h_105 : Litex.In _value_i6 (Litex.R (M := M)) := h_105
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i6 _value_i5 (M.real_subset_complex _ h_105) (M.real_subset_complex _ h_104))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i6 _value_i5 (M.real_subset_complex _ h_105) (M.real_subset_complex _ h_104))
    exact (Litex.addInR _value_i6 _value_i5 h_105 h_104))))
theorem h_195 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_196 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

theorem h_198 : Litex.Same (_object_i1 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _pointwise : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_213 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_214 : Litex.In _value_i8 (Litex.R (M := M))), (by
            let _object_w10 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) _value_i7 _value_i8 (h_89 (M := M)) h_213 h_214 True.intro)
            let _object_w11 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (_object_i4 (M := M)) _value_i7 _value_i8 (h_195 (M := M)) h_213 h_214 True.intro)
            exact (by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w11
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) := (by
            intro _Host_i7 _rep_i7 _value_i7 h_213 _Host_i8 _rep_i8 _value_i8 h_214
            let _object_w10 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) _value_i7 _value_i8 (h_89 (M := M)) h_213 h_214 True.intro)
            let _object_w11 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (_object_i4 (M := M)) _value_i7 _value_i8 (h_195 (M := M)) h_213 h_214 True.intro)
            have h_200 : (by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w11
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w10;
                    let _equal_wd_1_1 := _object_w11;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i7)) := (let _equal_wd_2_0 := (Litex.add _value_i7 _value_i8 (M.real_subset_complex _ h_213) (M.real_subset_complex _ h_214));
                      let _equal_wd_2_1 := (Litex.add _value_i8 _value_i7 (M.real_subset_complex _ h_214) (M.real_subset_complex _ h_213));
                      (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_213)) + (Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_214))) ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_214)) + (Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_213))) (Litex.NativeBridge.denoteAdd _value_i7 _value_i8 (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 h_213)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_214))) (Litex.NativeBridge.denoteAdd _value_i8 _value_i7 (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_214)) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 h_213))) (by ring!))))
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := _value_i7;
                      let _wd_1_2 := _value_i8;
                      (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_213 h_214 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_90 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from rfl))
                    ))).trans (_litex_residual.trans ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i7)) from by
                      let _litex_original := _equal_wd_1_1
                      let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                      let _wd_1_1 := _value_i7;
                      let _wd_1_2 := _value_i8;
                      (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_213 h_214 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_196 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue _raw_i6 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue _raw_i6 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue _raw_i6 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i7)) from rfl))
                    ))).symm))))
                  )
              )
            exact h_200
          )
          apply Litex.functionExtOnDomain (_object_i1 (M := M)) (_object_i4 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) ((h_90 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i4 (M := M)) (_object_i4 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True))) ((h_196 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i4 (M := M)))) (by rfl)
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
            have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
            have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))
          have _repack : _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) := (by
            apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
            apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
            funext i
            fin_cases i <;> norm_num [Litex.FiniteFunction.index])
          exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) x) _repack) (_pointwise (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))
        )
      )
  )

noncomputable def _object_i9 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 _raw_i10)) (by
  intro _raw_i10 h_425 _positive_i10
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_425)
  have h_425 : Litex.In _value_i10 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i10).mpr ⟨h_425, _positive_i10⟩)
  have h_426 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i10 h_425)
        )
    )
  have h_427 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i10 h_426)
        )
    )
  have h_428 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i10 h_426) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i10 _value_i10 (Litex.positiveRealToComplex _value_i10 h_425) (Litex.positiveRealToComplex _value_i10 h_425))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i10 _value_i10 (Litex.positiveRealToComplex _value_i10 h_425) (Litex.positiveRealToComplex _value_i10 h_425))
    exact (Litex.addInR _value_i10 _value_i10 (Litex.inRPos_real _value_i10 h_425) (Litex.inRPos_real _value_i10 h_425)))))
theorem h_565 : Litex.In (_object_i9 (M := M)) (Litex.fnSet ((_object_i9 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i9 (M := M)))
      )
  )
theorem h_566 : Litex.Same (_object_i9 (M := M)) (_object_i9 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i9 (M := M)))
      )
  )

noncomputable def _object_i11 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)) (fun (_raw_i12 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i12)) (by
  intro _raw_i12 h_580 _positive_i12
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_580)
  have h_580 : Litex.In _value_i12 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i12).mpr ⟨h_580, _positive_i12⟩)
  have h_581 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i12 h_580)
        )
    )
  have h_582 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i12 h_581)
        )
    )
  have h_583 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i12 h_581) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i12 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i12 h_580))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i12 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i12 h_580))
    exact (Litex.mulInR (Litex.number (M := M) (2 : ℂ)) _value_i12 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.inRPos_real _value_i12 h_580)))))
theorem h_698 : Litex.In (_object_i11 (M := M)) (Litex.fnSet ((_object_i11 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i11 (M := M)))
      )
  )
theorem h_699 : Litex.Same (_object_i11 (M := M)) (_object_i11 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i11 (M := M)))
      )
  )

theorem h_701 : Litex.Same (_object_i9 (M := M)) (_object_i11 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _pointwise : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_716 : Litex.In _value_i13 (Litex.RPos (M := M))), (by
            let _object_w26 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) (_object_i9 (M := M)) _value_i13 (h_565 (M := M)) (Litex.inRPos_real _value_i13 h_716) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i13)).mp h_716).2)
            let _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)) (_object_i11 (M := M)) _value_i13 (h_698 (M := M)) (Litex.inRPos_real _value_i13 h_716) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i13)).mp h_716).2)
            exact (by
              let _equal_wd_1_0 := _object_w26
              let _equal_wd_1_1 := _object_w27
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) := (by
            intro _Host_i13 _rep_i13 _value_i13 h_716
            have h_717 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i13 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i13 h_716)
                  )
              )
            have h_718 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i13 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i13 h_717)
                  )
              )
            have h_719 : ¬ Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i13 h_717) _litex_zero.symm)
                  )
              )
            let _object_w26 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) (_object_i9 (M := M)) _value_i13 (h_565 (M := M)) (Litex.inRPos_real _value_i13 h_716) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i13)).mp h_716).2)
            let _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)) (_object_i11 (M := M)) _value_i13 (h_698 (M := M)) (Litex.inRPos_real _value_i13 h_716) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i13)).mp h_716).2)
            have h_703 : (by
              let _equal_wd_1_0 := _object_w26
              let _equal_wd_1_1 := _object_w27
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w26;
                    let _equal_wd_1_1 := _object_w27;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (Litex.denote _value_i13)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i13)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i13)) = (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i13)) := (let _equal_wd_2_0 := (Litex.add _value_i13 _value_i13 (Litex.positiveRealToComplex _value_i13 h_716) (Litex.positiveRealToComplex _value_i13 h_716));
                      let _equal_wd_2_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i13 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i13 h_716));
                      (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i13 (Litex.positiveRealToComplex _value_i13 h_716)) + (Litex.NativeBridge.asComplex _value_i13 (Litex.positiveRealToComplex _value_i13 h_716))) ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i13 (Litex.positiveRealToComplex _value_i13 h_716))) (Litex.NativeBridge.denoteAdd _value_i13 _value_i13 (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.positiveRealToComplex _value_i13 h_716)) (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.positiveRealToComplex _value_i13 h_716))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i13 (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.positiveRealToComplex _value_i13 h_716))) (by ring!))))
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (Litex.denote _value_i13)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (Litex.denote _value_i13)) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i13)) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i9 (M := M));
                      let _wd_1_1 := _value_i13;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_716) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_716).2))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_566 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 _raw_i10)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 _raw_i10)) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i13)) from rfl))
                    ))).trans (_litex_residual.trans ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i13)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i13)) = (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i13)) from by
                      let _litex_original := _equal_wd_1_1
                      let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                      let _wd_1_1 := _value_i13;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_716) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_716).2))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_699 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)) (fun (_raw_i12 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i12)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i12)) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i13)) from rfl))
                    ))).symm))))
                  )
              )
            exact h_703
          )
          apply Litex.functionExtOnDomain (_object_i9 (M := M)) (_object_i11 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12))) (Litex.inOfSame (_object_i9 (M := M)) (_object_i9 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)))) ((h_566 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i9 (M := M)))) (Litex.inOfSame (_object_i11 (M := M)) (_object_i11 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)))) ((h_699 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i11 (M := M)))) (by rfl)
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) _litex_input) _).mp _preimage_domain
          have _preimage_positive_i10 := _preimage_guard
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.RPos (M := M))) := ((Litex.positiveReal_members (M := M) _preimage_input).mpr ⟨_preimage_members, _preimage_positive_i10⟩)
          have _repack : _preimage_input = _preimage_input := rfl
          exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) x) _repack) (_pointwise (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_binary_x5f_sums_x2f_statement_x2e_lit
