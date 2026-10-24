import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_shifted_x5f_guarded_x5f_quotient_x5f_distribution_x2f_statement_x2e_lit

universe u v1 v8 v9 v10
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_2 : Litex.In _value_i1 (Litex.R (M := M))), (by
    let _object_w2 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_2) (Litex.numberInC (M := M) (1 : ℂ)))
    exact ¬ Litex.Same _object_w2 (Litex.number (M := M) (0 : ℂ))
  )

noncomputable def _object_i3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by
  intro _raw_i4 _raw_i5 h_47 h_48 h_16
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_47)
  have h_47 : Litex.In _value_i4 (Litex.R (M := M)) := h_47
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_48)
  have h_48 : Litex.In _value_i5 (Litex.R (M := M)) := h_48
  have h_16 : ((prop_1 (M := M)) _value_i5) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))
            exact h_16)
        )
    )
  have h_49 :=
    (Classical.choose (show ((prop_1 (M := M)) _value_i5) from h_16))
  have h_50 :=
    (Classical.choose_spec (show ((prop_1 (M := M)) _value_i5) from h_16))
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := _value_i4;
    let _wd_1_1 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i5 h_48) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_47) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.addInC _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_48) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact h_50)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := _value_i4;
    let _wd_1_1 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i5 h_48) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_47) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.addInC _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_48) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact h_50)))
    exact (Litex.divInR _value_i4 (_atomic_wd_1_0).val.right h_47 (Litex.addInR _value_i5 (Litex.number (M := M) (1 : ℂ)) h_48 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))) (_atomic_wd_1_0).wd.2.2))))
theorem h_183 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_184 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_187 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_192 : Litex.In _value_i8 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_193 : Litex.In _value_i9 (Litex.R (M := M))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_194 : Litex.In _value_i10 (Litex.R (M := M))) (h_185 : ((prop_1 (M := M)) _value_i10)), (by
  let _equal_wd_1_0 := (let _object_w16 := (Litex.add _value_i8 _value_i9 (M.real_subset_complex _ h_192) (M.real_subset_complex _ h_193));
  let _wd_1_1 := _value_i10;
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w16 _wd_1_1 (h_183 (M := M)) (by
    let _atomic_wd_1_0 := _object_w16
    exact (Litex.addInR _value_i8 _value_i9 h_192 h_193)) h_194 h_185))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _value_i8 _value_i10 (h_183 (M := M)) h_192 h_194 h_185);
  let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _value_i9 _value_i10 (h_183 (M := M)) h_193 h_194 h_185);
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
          intro _Host_i8 _rep_i8 _value_i8 h_192 _Host_i9 _rep_i9 _value_i9 h_193 _Host_i10 _rep_i10 _value_i10 h_194 h_185
          have h_195 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i10) from h_185))
          have h_196 :=
            (Classical.choose_spec (show ((prop_1 (M := M)) _value_i10) from h_185))
          have h_587 : Litex.In _value_i8 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_192
                )
            )
          have h_588 : Litex.In _value_i9 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_193
                )
            )
          have h_589 : Litex.In _value_i10 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_194
                )
            )
          have h_590 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i10) from h_185))
          have h_591 :=
            (Classical.choose_spec (show ((prop_1 (M := M)) _value_i10) from h_185))
          let _object_w29 := (let _object_w20 := (Litex.add _value_i8 _value_i9 (M.real_subset_complex _ h_587) (M.real_subset_complex _ h_588));
          let _wd_1_1 := _value_i10;
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w20 _wd_1_1 (h_183 (M := M)) (by
            let _atomic_wd_1_0 := _object_w20
            exact (Litex.addInR _value_i8 _value_i9 h_587 h_588)) h_589 h_185))

          let _object_w30 := (let _wd_1_0 := (Litex.add _value_i8 _value_i9 (M.real_subset_complex _ h_587) (M.real_subset_complex _ h_588));
          let _wd_1_1 := (Litex.add _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i10 h_589) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i8 _value_i9 (M.real_subset_complex _ h_587) (M.real_subset_complex _ h_588))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_589) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_591)))

          have h_188 : (by
            let _equal_wd_1_0 := _object_w29
            let _equal_wd_1_1 := _object_w30
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w29;
                  let _equal_wd_1_1 := _object_w30;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)), (Litex.denote _value_i10)])) = (M.divValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)), (Litex.denote _value_i10)])))).trans (by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
                    let _object_w28 := (_equal_wd_1_1).val.left;
                    let _wd_1_2 := _value_i10;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _object_w28 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _object_w28
                      exact (Litex.addInR _value_i8 _value_i9 h_587 h_588)) h_589 h_185))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_184 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w31 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _value_i8 _value_i10 (h_183 (M := M)) h_587 h_589 h_185)

          let _object_w32 := (let _wd_1_0 := _value_i8;
          let _wd_1_1 := (_object_w30).val.right;
          (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_587) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_589) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_591)))

          have h_189 : (by
            let _equal_wd_1_0 := _object_w31
            let _equal_wd_1_1 := _object_w32
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w31;
                  let _equal_wd_1_1 := _object_w32;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i10)])) = (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from by
                    have _litex_residual : (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i10)])))).trans (by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
                    let _wd_1_1 := _value_i8;
                    let _wd_1_2 := _value_i10;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_587 h_589 h_185))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_184 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w33 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _value_i9 _value_i10 (h_183 (M := M)) h_588 h_589 h_185)

          let _object_w34 := (let _wd_1_0 := _value_i9;
          let _wd_1_1 := (_object_w32).val.right;
          (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_588) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_589) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_591)))

          have h_190 : (by
            let _equal_wd_1_0 := _object_w33
            let _equal_wd_1_1 := _object_w34
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w33;
                  let _equal_wd_1_1 := _object_w34;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from by
                    have _litex_residual : (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])))).trans (by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
                    let _wd_1_1 := _value_i9;
                    let _wd_1_2 := _value_i10;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_588 h_589 h_185))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_184 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w35 := (let _wd_1_0 := _object_w32;
          let _wd_1_1 := _object_w34;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w32
            exact (Litex.divInC _value_i8 (_object_w34).val.right (M.real_subset_complex _ h_587) (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_589) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (by
            let _atomic_wd_1_0 := _object_w34
            exact (Litex.divInC _value_i9 (_object_w34).val.right (M.real_subset_complex _ h_588) (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_589) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2))))

          have h_191 : (by
            let _equal_wd_1_0 := _object_w30
            let _equal_wd_1_1 := _object_w35
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w30;
                  let _equal_wd_1_1 := _object_w35;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_587)) + (Litex.NativeBridge.asComplex _value_i9 (Litex.realToComplex _value_i9 h_588))) / ((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_589)) + (1 : ℂ))) (((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_587)) / ((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_589)) + (1 : ℂ))) + ((Litex.NativeBridge.asComplex _value_i9 (Litex.realToComplex _value_i9 h_588)) / ((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_589)) + (1 : ℂ)))) (Litex.NativeBridge.denoteDiv (_object_w30).val.left (_object_w30).val.right (_object_w30).wd.1 (_object_w30).wd.2.1 (_object_w30).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i8 _value_i9 ((_object_w30).val.left).wd.1 ((_object_w30).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_587)) (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.realToComplex _value_i9 h_588))) (Litex.NativeBridge.denoteAdd _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i10 h_589) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_589)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteDiv _value_i8 (_object_w32).val.right (_object_w32).wd.1 (_object_w32).wd.2.1 (_object_w32).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_587)) (Litex.NativeBridge.denoteAdd _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i10 h_589) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_589)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteDiv _value_i9 (_object_w34).val.right (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.realToComplex _value_i9 h_588)) (Litex.NativeBridge.denoteAdd _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i10 h_589) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_589)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))) (by
                    have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_589)) + (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_object_w34).val.right ((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_589)) + (1 : ℂ)) (Litex.NativeBridge.denoteAdd _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i10 h_589) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_589)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
                    let _atomic_wd_1_0 := (_object_w34).val.right
                    exact h_591)
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (Eq.trans ((h_188).trans h_191) (Eq.trans (congrArg₂ M.addValue (show (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i10)])) from (h_189).symm) (show (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) from (h_190).symm)) (show @Eq M.Value _ _ from Eq.refl _)))
        )
      )
  )

theorem h_7429 : ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Exists.intro (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (by
          let _atomic_wd_2_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
          exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) ((1 : ℂ) + (1 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

theorem h_7440 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_7429 (M := M)) with ⟨h_2, h_1⟩; exact h_2)
      )
  )

theorem h_7441 : ¬ Litex.Same (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_7429 (M := M)) with ⟨h_2, h_1⟩; exact h_1)
      )
  )

noncomputable def _object_i12 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))))
theorem h_7614 : Litex.Same (_object_i12 (M := M)) (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))))) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
        let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))))))
      )
  )

theorem h_7615 : (by
  have h_7618 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (h_7440 (M := M))
        )
    )
  have h_7619 : ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (h_7429 (M := M))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _object_w47 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w47 _wd_1_1 (h_183 (M := M)) (by
      let _atomic_wd_1_0 := _object_w47
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_object_w47).wd.1 (_object_w47).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (4 : ℂ)) (6 : ℝ) (by norm_num)))) h_7618 h_7619))
    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
    let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_7616 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_7617 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
                )
            )
          have h_7618 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_7440 (M := M))
                )
            )
          have h_7619 : ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_7429 (M := M))
                )
            )
          have h_7643 :=
            (Classical.choose (show ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) from h_7619))
          have h_7644 :=
            (Classical.choose_spec (show ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) from h_7619))
          have h_7620 : Litex.Same (let _object_w47 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w47 _wd_1_1 (h_183 (M := M)) (by
            let _atomic_wd_1_0 := _object_w47
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_object_w47).wd.1 (_object_w47).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (4 : ℂ)) (6 : ℝ) (by norm_num)))) h_7618 h_7619)) (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
          let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_187 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_7616 (Litex.number (M := M) (4 : ℂ)) h_7617 (Litex.number (M := M) (1 : ℂ)) h_7618 h_7619)
                )
            )
          exact (let _equal_wd_1_0 := (let _object_w47 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w47 _wd_1_1 (h_183 (M := M)) (by
          let _atomic_wd_1_0 := _object_w47
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_object_w47).wd.1 (_object_w47).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (4 : ℂ)) (6 : ℝ) (by norm_num)))) h_7618 h_7619));
        let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
        let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_7620).trans (Litex.sameRefl _equal_wd_1_1)))))
        )
      )
  )

noncomputable def _object_w51 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)))

theorem h_7725 : (by
  let _equal_wd_1_0 := (_object_w51 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w51 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (1 : ℂ))])) = (M.number (1 : ℂ)) from by
          have _litex_residual : (M.divValue (M.number (2 : ℂ)) (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = (M.number (1 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (h_7441 (M := M)))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) ((2 : ℂ) / ((1 : ℂ) + (1 : ℂ))) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (1 : ℂ))])))).trans (by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M))))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_184 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.number (2 : ℂ)) (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w52 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)))

theorem h_7828 : (by
  let _equal_wd_1_0 := (_object_w52 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w52 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (4 : ℂ)), (M.number (1 : ℂ))])) = (M.number (2 : ℂ)) from by
          have _litex_residual : (M.divValue (M.number (4 : ℂ)) (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = (M.number (2 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (h_7441 (M := M)))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) ((4 : ℂ) / ((1 : ℂ) + (1 : ℂ))) (2 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (4 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (4 : ℂ)), (M.number (1 : ℂ))])))).trans (by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M))))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_184 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.number (4 : ℂ)) (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w54 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))

theorem h_7931 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
  let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_183 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_7440 (M := M)) (h_7429 (M := M)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (_object_w54 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (congrArg₂ M.addValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (1 : ℂ))])) = (M.number (1 : ℂ)) from (h_7725 (M := M))) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (4 : ℂ)), (M.number (1 : ℂ))])) = (M.number (2 : ℂ)) from (h_7828 (M := M))))
      )
  )

theorem h_7951 : Litex.Same (_object_i12 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_2_0 := (_object_w54 (M := M));
        (show Litex.Same (_object_i12 (M := M)) (Litex.number (M := M) (3 : ℂ)) from (Eq.trans (((h_7614 (M := M))).trans (h_7931 (M := M))) (Eq.trans (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((1 : ℂ) + (2 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w54 (M := M))).wd.1 ((_object_w54 (M := M))).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (show @Eq M.Value _ _ from Eq.refl _)))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_shifted_x5f_guarded_x5f_quotient_x5f_distribution_x2f_statement_x2e_lit
