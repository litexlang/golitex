import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_guarded_x5f_quotients_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (by
  rintro _raw_i2 _raw_i3 h_76 h_77 ⟨h_1, h_2⟩
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_76)
  have h_76 : Litex.In _value_i2 (Litex.R (M := M)) := h_76
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_77)
  have h_77 : Litex.In _value_i3 (Litex.R (M := M)) := h_77
  have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i3 = (M.number (0 : ℂ))))
            exact h_1)
        )
    )
  have h_2 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i2 = (M.number (0 : ℂ))))
            exact h_2)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i2 _value_i3 (M.real_subset_complex _ h_76) (M.real_subset_complex _ h_77) h_1)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i2 _value_i3 (M.real_subset_complex _ h_76) (M.real_subset_complex _ h_77) h_1)
    exact (Litex.divInR _value_i2 _value_i3 h_76 h_77 (_atomic_wd_1_0).wd.2.2))))
theorem h_163 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_164 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i8 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))) (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.mulValue _raw_i9 (M.divValue (M.number (1 : ℂ)) _raw_i10))) (by
  rintro _raw_i9 _raw_i10 h_240 h_241 ⟨h_165, h_166⟩
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_240)
  have h_240 : Litex.In _value_i9 (Litex.R (M := M)) := h_240
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_241)
  have h_241 : Litex.In _value_i10 (Litex.R (M := M)) := h_241
  have h_165 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i9 = (M.number (0 : ℂ))))
            exact h_165)
        )
    )
  have h_166 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i10 = (M.number (0 : ℂ))))
            exact h_166)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := _value_i9;
    let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_241) h_166);
    (Litex.mul _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_240) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_241) (_atomic_wd_2_0).wd.2.2))))
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := _value_i9;
    let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_241) h_166);
    (Litex.mul _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_240) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_241) (_atomic_wd_2_0).wd.2.2))))
    exact (Litex.mulInC _value_i9 (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_240) (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_241) ((_atomic_wd_1_0).val.right).wd.2.2)))))
theorem h_494 : Litex.In (_object_i8 (M := M)) (Litex.fnSet ((_object_i8 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i8 (M := M)))
      )
  )
theorem h_495 : Litex.Same (_object_i8 (M := M)) (_object_i8 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i8 (M := M)))
      )
  )

theorem h_497 : Litex.Same (_object_i1 (M := M)) (_object_i8 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_504 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_517 : Litex.In _value_i15 (Litex.R (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_518 : Litex.In _value_i16 (Litex.R (M := M))) (h_498 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ))) (h_499 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i15 (Litex.R (M := M))) ∧ (((Litex.In _value_i16 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))))))) := (by
            intro _Host_i15 _rep_i15 _value_i15 h_517 _Host_i16 _rep_i16 _value_i16 h_518 h_498 h_499
            have h_500 : Litex.In _value_i15 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_517
                  )
              )
            have h_501 : Litex.In _value_i16 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_518
                  )
              )
            have h_502 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_499
                  )
              )
            have h_503 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_498
                  )
              )
            exact (And.intro h_500 (And.intro h_501 (And.intro h_502 h_503)))
          )
          have h_546 : ∀ {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_559 : Litex.In _value_i17 (Litex.R (M := M))) {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_560 : Litex.In _value_i18 (Litex.R (M := M))) (h_540 : ¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ))) (h_541 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i17 (Litex.R (M := M))) ∧ (((Litex.In _value_i18 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ)))))))) := (by
            intro _Host_i17 _rep_i17 _value_i17 h_559 _Host_i18 _rep_i18 _value_i18 h_560 h_540 h_541
            have h_542 : Litex.In _value_i17 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_559
                  )
              )
            have h_543 : Litex.In _value_i18 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_560
                  )
              )
            have h_544 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_541
                  )
              )
            have h_545 : ¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_540
                  )
              )
            exact (And.intro h_542 (And.intro h_543 (And.intro h_544 h_545)))
          )
          have _pointwise : ∀ {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_598 : Litex.In _value_i19 (Litex.R (M := M))) {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_599 : Litex.In _value_i20 (Litex.R (M := M))) (h_582 : ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))) (h_583 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ))), (by
            let _object_w27 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))) (_object_i1 (M := M)) _value_i19 _value_i20 (h_163 (M := M)) h_598 h_599 (And.intro h_582 h_583))
            let _object_w28 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))) (_object_i8 (M := M)) _value_i19 _value_i20 (h_494 (M := M)) h_598 h_599 (And.intro h_583 h_582))
            exact (by
              let _equal_wd_1_0 := _object_w27
              let _equal_wd_1_1 := _object_w28
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) := (by
            intro _Host_i19 _rep_i19 _value_i19 h_598 _Host_i20 _rep_i20 _value_i20 h_599 h_582 h_583
            let _object_w27 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))) (_object_i1 (M := M)) _value_i19 _value_i20 (h_163 (M := M)) h_598 h_599 (And.intro h_582 h_583))
            let _object_w28 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))) (_object_i8 (M := M)) _value_i19 _value_i20 (h_494 (M := M)) h_598 h_599 (And.intro h_583 h_582))
            have h_585 : (by
              let _equal_wd_1_0 := _object_w27
              let _equal_wd_1_1 := _object_w28
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w27;
                    let _equal_wd_1_1 := _object_w28;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i19), (Litex.denote _value_i20)])) = (M.divValue (Litex.denote _value_i19) (Litex.denote _value_i20)) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := _value_i19;
                      let _wd_1_2 := _value_i20;
                      (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_598 h_599 (And.intro h_582 h_583)))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_164 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (Litex.denote _value_i19) (Litex.denote _value_i20)) from rfl))
                    )).trans (((let _equal_wd_2_0 := (Litex.div _value_i19 _value_i20 (M.real_subset_complex _ h_598) (M.real_subset_complex _ h_599) h_582);
                    let _equal_wd_2_1 := (let _wd_1_0 := _value_i19;
                    let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_599) h_582);
                    (Litex.mul _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_598) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_599) (_atomic_wd_1_0).wd.2.2))));
                    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i19 (Litex.realToComplex _value_i19 h_598)) / (Litex.NativeBridge.asComplex _value_i20 (Litex.realToComplex _value_i20 h_599))) ((Litex.NativeBridge.asComplex _value_i19 (Litex.realToComplex _value_i19 h_598)) * ((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i20 (Litex.realToComplex _value_i20 h_599)))) (Litex.NativeBridge.denoteDiv _value_i19 _value_i20 (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.realToComplex _value_i19 h_598)) (Litex.NativeBridge.asComplex_spec _value_i20 (Litex.realToComplex _value_i20 h_599))) (Litex.NativeBridge.denoteMul _value_i19 (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.realToComplex _value_i19 h_598)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) _value_i20 ((_equal_wd_2_1).val.right).wd.1 ((_equal_wd_2_1).val.right).wd.2.1 ((_equal_wd_2_1).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i20 (Litex.realToComplex _value_i20 h_599)))) (by
                      have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i20 (Litex.realToComplex _value_i20 h_599)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i20 (Litex.NativeBridge.asComplex _value_i20 (Litex.realToComplex _value_i20 h_599)) (Litex.NativeBridge.asComplex_spec _value_i20 (Litex.realToComplex _value_i20 h_599)) h_582
                      litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                    ))))).trans ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i19), (Litex.denote _value_i20)])) = (M.mulValue (Litex.denote _value_i19) (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i20))) from by
                      let _litex_original := _equal_wd_1_1
                      let _litex_literal := (let _wd_1_0 := (_object_i8 (M := M));
                      let _wd_1_1 := _value_i19;
                      let _wd_1_2 := _value_i20;
                      (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_598 h_599 (And.intro h_583 h_582)))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_495 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))) (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.mulValue _raw_i9 (M.divValue (M.number (1 : ℂ)) _raw_i10))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.mulValue _raw_i9 (M.divValue (M.number (1 : ℂ)) _raw_i10))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.complex) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.mulValue _raw_i9 (M.divValue (M.number (1 : ℂ)) _raw_i10))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i19) (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i20))) from rfl))
                    )).symm))))
                  )
              )
            exact h_585
          )
          apply Litex.functionExtOnDomain (_object_i1 (M := M)) (_object_i8 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ)))))))) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))))) ((h_164 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i8 (M := M)) (_object_i8 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))))) ((h_495 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i8 (M := M)))) (Litex.SetSemantics.ext ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))))).domain_isSet ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))))).domain from by
            intro _preimage_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
            rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
            have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
            have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
            have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))
            have _domain_target := h_504 (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0 _preimage_guard_1
            have _repack : _preimage_input = (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))) := (show _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) from (by
            apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
            apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
            funext i
            fin_cases i <;> norm_num [Litex.FiniteFunction.index]))
            exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))).mpr ⟨(And.left _domain_target), (And.left (And.right _domain_target)), (And.intro (And.left (And.right (And.right _domain_target))) (And.right (And.right (And.right _domain_target))))⟩)
          ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))))).domain from by
            intro _preimage_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i9 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i10 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
            rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
            have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
            have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
            have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))
            have _domain_target := h_546 (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0 _preimage_guard_1
            have _repack : _preimage_input = (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))) := (show _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) from (by
            apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
            apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
            funext i
            fin_cases i <;> norm_num [Litex.FiniteFunction.index]))
            exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))).mpr ⟨(And.left _domain_target), (And.left (And.right _domain_target)), (And.intro (And.left (And.right (And.right _domain_target))) (And.right (And.right (And.right _domain_target))))⟩)
          ) x hx⟩))
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
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
          exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) x) _repack) (_pointwise (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0 _preimage_guard_1)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_guarded_x5f_quotients_x2f_statement_x2e_lit
