import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_quotient_x5f_distributes_x2f_statement_x2e_lit

universe u v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (by
  intro _raw_i2 _raw_i3 h_44 h_45 h_1
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_44)
  have h_44 : Litex.In _value_i2 (Litex.R (M := M)) := h_44
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_45)
  have h_45 : Litex.In _value_i3 (Litex.R (M := M)) := h_45
  have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i3 = (M.number (0 : ℂ))))
            exact h_1)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i2 _value_i3 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45) h_1)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i2 _value_i3 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45) h_1)
    exact (Litex.divInR _value_i2 _value_i3 h_44 h_45 (_atomic_wd_1_0).wd.2.2))))
theorem h_129 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_130 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w8 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_129 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_131 : (by
  let _equal_wd_1_0 := (_object_w8 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w8 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (2 : ℂ))])) = (M.number (3 : ℂ)) from by
          have _litex_residual : (M.divValue (M.number (6 : ℂ)) (M.number (2 : ℂ))) = (M.number (3 : ℂ)) := (let _equal_wd_2_0 := (Litex.div (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((6 : ℂ) / (2 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (2 : ℂ))])))).trans (by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_2 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_130 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.number (6 : ℂ)) (M.number (2 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_188 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_193 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_194 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_195 : Litex.In _value_i8 (Litex.R (M := M))) (h_186 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))), (by
  let _equal_wd_1_0 := (let _object_w12 := (Litex.add _value_i6 _value_i7 (M.real_subset_complex _ h_193) (M.real_subset_complex _ h_194));
  let _wd_1_1 := _value_i8;
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w12 _wd_1_1 (h_129 (M := M)) (by
    let _atomic_wd_1_0 := _object_w12
    exact (Litex.addInR _value_i6 _value_i7 h_193 h_194)) h_195 h_186))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i6 _value_i8 (h_129 (M := M)) h_193 h_195 h_186);
  let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i7 _value_i8 (h_129 (M := M)) h_194 h_195 h_186);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_193 _Host_i7 _rep_i7 _value_i7 h_194 _Host_i8 _rep_i8 _value_i8 h_195 h_186
          have h_546 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_193
                )
            )
          have h_547 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_194
                )
            )
          have h_548 : Litex.In _value_i8 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_195
                )
            )
          let _object_w24 := (let _object_w15 := (Litex.add _value_i6 _value_i7 (M.real_subset_complex _ h_546) (M.real_subset_complex _ h_547));
          let _wd_1_1 := _value_i8;
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w15 _wd_1_1 (h_129 (M := M)) (by
            let _atomic_wd_1_0 := _object_w15
            exact (Litex.addInR _value_i6 _value_i7 h_546 h_547)) h_548 h_186))

          let _object_w25 := (let _wd_1_0 := (Litex.add _value_i6 _value_i7 (M.real_subset_complex _ h_546) (M.real_subset_complex _ h_547));
          let _wd_1_1 := _value_i8;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i6 _value_i7 (M.real_subset_complex _ h_546) (M.real_subset_complex _ h_547))) (M.real_subset_complex _ h_548) h_186))

          have h_189 : (by
            let _equal_wd_1_0 := _object_w24
            let _equal_wd_1_1 := _object_w25
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w24;
                  let _equal_wd_1_1 := _object_w25;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])) = (M.divValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) = (M.divValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)), (Litex.denote _value_i8)])))).trans (by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _object_w23 := (_equal_wd_1_1).val.left;
                    let _wd_1_2 := _value_i8;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _wd_1_0 _object_w23 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _object_w23
                      exact (Litex.addInR _value_i6 _value_i7 h_546 h_547)) h_548 h_186))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_130 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.addValue (Litex.denote _value_i6) (Litex.denote _value_i7)) (Litex.denote _value_i8)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w26 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i6 _value_i8 (h_129 (M := M)) h_546 h_548 h_186)

          let _object_w27 := (Litex.div _value_i6 _value_i8 (M.real_subset_complex _ h_546) (M.real_subset_complex _ h_548) h_186)

          have h_190 : (by
            let _equal_wd_1_0 := _object_w26
            let _equal_wd_1_1 := _object_w27
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w26;
                  let _equal_wd_1_1 := _object_w27;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i8)])) = (M.divValue (Litex.denote _value_i6) (Litex.denote _value_i8)) from by
                    have _litex_residual : (M.divValue (Litex.denote _value_i6) (Litex.denote _value_i8)) = (M.divValue (Litex.denote _value_i6) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i8)])))).trans (by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i6;
                    let _wd_1_2 := _value_i8;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_546 h_548 h_186))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_130 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (Litex.denote _value_i6) (Litex.denote _value_i8)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w28 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i7 _value_i8 (h_129 (M := M)) h_547 h_548 h_186)

          let _object_w29 := (Litex.div _value_i7 _value_i8 (M.real_subset_complex _ h_547) (M.real_subset_complex _ h_548) h_186)

          have h_191 : (by
            let _equal_wd_1_0 := _object_w28
            let _equal_wd_1_1 := _object_w29
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w28;
                  let _equal_wd_1_1 := _object_w29;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) = (M.divValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from by
                    have _litex_residual : (M.divValue (Litex.denote _value_i7) (Litex.denote _value_i8)) = (M.divValue (Litex.denote _value_i7) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])))).trans (by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i7;
                    let _wd_1_2 := _value_i8;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_547 h_548 h_186))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_130 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (Litex.denote _value_i7) (Litex.denote _value_i8)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w30 := (let _wd_1_0 := _object_w27;
          let _wd_1_1 := _object_w29;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w27
            exact (Litex.divInC _value_i6 _value_i8 (M.real_subset_complex _ h_546) (M.real_subset_complex _ h_548) (_atomic_wd_1_0).wd.2.2)) (by
            let _atomic_wd_1_0 := _object_w29
            exact (Litex.divInC _value_i7 _value_i8 (M.real_subset_complex _ h_547) (M.real_subset_complex _ h_548) (_atomic_wd_1_0).wd.2.2))))

          have h_192 : (by
            let _equal_wd_1_0 := _object_w25
            let _equal_wd_1_1 := _object_w30
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w25;
                  let _equal_wd_1_1 := _object_w30;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_546)) + (Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_547))) / (Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_548))) (((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_546)) / (Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_548))) + ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_547)) / (Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_548)))) (Litex.NativeBridge.denoteDiv (_object_w25).val.left _value_i8 (_object_w25).wd.1 (_object_w25).wd.2.1 (_object_w25).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i6 _value_i7 ((_object_w25).val.left).wd.1 ((_object_w25).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_546)) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 h_547))) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_548))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteDiv _value_i6 _value_i8 (_object_w27).wd.1 (_object_w27).wd.2.1 (_object_w27).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_546)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_548))) (Litex.NativeBridge.denoteDiv _value_i7 _value_i8 (_object_w29).wd.1 (_object_w29).wd.2.1 (_object_w29).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 h_547)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_548)))) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_548)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i8 (Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_548)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_548)) h_186
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (Eq.trans ((h_189).trans h_192) (Eq.trans (congrArg₂ M.addValue (show (M.divValue (Litex.denote _value_i6) (Litex.denote _value_i8)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), (Litex.denote _value_i8)])) from (h_190).symm) (show (M.divValue (Litex.denote _value_i7) (Litex.denote _value_i8)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i8)])) from (h_191).symm)) (show @Eq M.Value _ _ from Eq.refl _)))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_quotient_x5f_distributes_x2f_statement_x2e_lit
