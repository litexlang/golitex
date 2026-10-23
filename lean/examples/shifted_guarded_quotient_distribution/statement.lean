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
    let _wd_1_1 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_48) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_47) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.addInC _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_48) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact h_50)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := _value_i4;
    let _wd_1_1 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_48) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_47) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.addInC _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_48) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact h_50)))
    exact (Litex.divInR _value_i4 (_atomic_wd_1_0).val.right h_47 (Litex.addInR _value_i5 (Litex.number (M := M) (1 : ℂ)) h_48 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))) (_atomic_wd_1_0).wd.2.2))))
theorem h_345 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_346 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_349 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_354 : Litex.In _value_i8 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_355 : Litex.In _value_i9 (Litex.R (M := M))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_356 : Litex.In _value_i10 (Litex.R (M := M))) (h_347 : ((prop_1 (M := M)) _value_i10)), (by
  let _equal_wd_1_0 := (let _object_w10 := (Litex.add _value_i8 _value_i9 (M.real_subset_complex _ h_354) (M.real_subset_complex _ h_355));
  let _wd_1_1 := _value_i10;
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w10 _wd_1_1 (h_345 (M := M)) (by
    let _atomic_wd_1_0 := _object_w10
    exact (Litex.addInR _value_i8 _value_i9 h_354 h_355)) h_356 h_347))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _value_i8 _value_i10 (h_345 (M := M)) h_354 h_356 h_347);
  let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _value_i9 _value_i10 (h_345 (M := M)) h_355 h_356 h_347);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    intro _Host_i8 _rep_i8 _value_i8 h_354 _Host_i9 _rep_i9 _value_i9 h_355 _Host_i10 _rep_i10 _value_i10 h_356 h_347
    have h_357 :=
      (Classical.choose (show ((prop_1 (M := M)) _value_i10) from h_347))
    have h_358 :=
      (Classical.choose_spec (show ((prop_1 (M := M)) _value_i10) from h_347))
    have h_749 : Litex.In _value_i8 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_354
          )
      )
    have h_750 : Litex.In _value_i9 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_355
          )
      )
    have h_751 : Litex.In _value_i10 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_356
          )
      )
    have h_752 :=
      (Classical.choose (show ((prop_1 (M := M)) _value_i10) from h_347))
    have h_753 :=
      (Classical.choose_spec (show ((prop_1 (M := M)) _value_i10) from h_347))
    let _object_w21 := (let _object_w12 := (Litex.add _value_i8 _value_i9 (M.real_subset_complex _ h_749) (M.real_subset_complex _ h_750));
    let _wd_1_1 := _value_i10;
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w12 _wd_1_1 (h_345 (M := M)) (by
      let _atomic_wd_1_0 := _object_w12
      exact (Litex.addInR _value_i8 _value_i9 h_749 h_750)) h_751 h_347))

    let _object_w22 := (let _wd_1_0 := (Litex.add _value_i8 _value_i9 (M.real_subset_complex _ h_749) (M.real_subset_complex _ h_750));
    let _wd_1_1 := (Litex.add _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_751) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.addInC _value_i8 _value_i9 (M.real_subset_complex _ h_749) (M.real_subset_complex _ h_750))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_751) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact h_753)))

    have h_350 : (by
      let _equal_wd_1_0 := _object_w21
      let _equal_wd_1_1 := _object_w22
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w21;
            let _equal_wd_1_1 := _object_w22;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)), (Litex.denote _value_i10)])) = (M.divValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from by
              have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)), (Litex.denote _value_i10)])))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
              let _object_w20 := (_equal_wd_1_1).val.left;
              let _wd_1_2 := _value_i10;
              (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _object_w20 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (by
                let _atomic_wd_1_0 := _object_w20
                exact (Litex.addInR _value_i8 _value_i9 h_749 h_750)) h_751 h_347))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_346 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w23 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _value_i8 _value_i10 (h_345 (M := M)) h_749 h_751 h_347)

    let _object_w24 := (let _wd_1_0 := _value_i8;
    let _wd_1_1 := (_object_w22).val.right;
    (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_749) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_751) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact h_753)))

    have h_351 : (by
      let _equal_wd_1_0 := _object_w23
      let _equal_wd_1_1 := _object_w24
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w23;
            let _equal_wd_1_1 := _object_w24;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i10)])) = (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from by
              have _litex_residual : (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i10)])))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
              let _wd_1_1 := _value_i8;
              let _wd_1_2 := _value_i10;
              (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_749 h_751 h_347))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_346 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w25 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _value_i9 _value_i10 (h_345 (M := M)) h_750 h_751 h_347)

    let _object_w26 := (let _wd_1_0 := _value_i9;
    let _wd_1_1 := (_object_w24).val.right;
    (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_750) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_751) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact h_753)))

    have h_352 : (by
      let _equal_wd_1_0 := _object_w25
      let _equal_wd_1_1 := _object_w26
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w25;
            let _equal_wd_1_1 := _object_w26;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from by
              have _litex_residual : (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
              let _wd_1_1 := _value_i9;
              let _wd_1_2 := _value_i10;
              (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_750 h_751 h_347))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_346 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w27 := (let _wd_1_0 := _object_w24;
    let _wd_1_1 := _object_w26;
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w24
      exact (Litex.divInC _value_i8 (_object_w26).val.right (M.real_subset_complex _ h_749) (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_751) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (by
      let _atomic_wd_1_0 := _object_w26
      exact (Litex.divInC _value_i9 (_object_w26).val.right (M.real_subset_complex _ h_750) (Litex.addInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_751) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2))))

    have h_353 : (by
      let _equal_wd_1_0 := _object_w22
      let _equal_wd_1_1 := _object_w27
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w22;
            let _equal_wd_1_1 := _object_w27;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_749)) + (Litex.NativeBridge.asComplex _value_i9 (Litex.realToComplex _value_i9 h_750))) / ((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_751)) + (1 : ℂ))) (((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_749)) / ((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_751)) + (1 : ℂ))) + ((Litex.NativeBridge.asComplex _value_i9 (Litex.realToComplex _value_i9 h_750)) / ((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_751)) + (1 : ℂ)))) (Litex.NativeBridge.denoteDiv (_object_w22).val.left (_object_w22).val.right (_object_w22).wd.1 (_object_w22).wd.2.1 (_object_w22).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i8 _value_i9 ((_object_w22).val.left).wd.1 ((_object_w22).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_749)) (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.realToComplex _value_i9 h_750))) (Litex.NativeBridge.denoteAdd _value_i10 (Litex.number (M := M) (1 : ℂ)) ((_object_w22).val.right).wd.1 ((_object_w22).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_751)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteDiv _value_i8 (_object_w24).val.right (_object_w24).wd.1 (_object_w24).wd.2.1 (_object_w24).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_749)) (Litex.NativeBridge.denoteAdd _value_i10 (Litex.number (M := M) (1 : ℂ)) ((_object_w24).val.right).wd.1 ((_object_w24).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_751)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteDiv _value_i9 (_object_w26).val.right (_object_w26).wd.1 (_object_w26).wd.2.1 (_object_w26).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.realToComplex _value_i9 h_750)) (Litex.NativeBridge.denoteAdd _value_i10 (Litex.number (M := M) (1 : ℂ)) ((_object_w26).val.right).wd.1 ((_object_w26).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_751)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))) (by
              have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_751)) + (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_object_w26).val.right ((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_751)) + (1 : ℂ)) (Litex.NativeBridge.denoteAdd _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_751) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_751)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
              let _atomic_wd_1_0 := (_object_w26).val.right
              exact h_753)
              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
            ))))
          )
      )
    exact (Eq.trans ((h_350).trans h_353) (Eq.trans (congrArg₂ M.addValue (show (M.divValue (Litex.denote _value_i8) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i10)])) from (h_351).symm) (show (M.divValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) from (h_352).symm)) (show @Eq M.Value _ _ from Eq.refl _)))
  )

theorem h_9415 : ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) :=
  (Exists.intro (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (by
    let _atomic_wd_2_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) ((1 : ℂ) + (1 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_9426 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
  (by rcases (h_9415 (M := M)) with ⟨h_2, h_1⟩; exact h_2)

theorem h_9427 : ¬ Litex.Same (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) :=
  (by rcases (h_9415 (M := M)) with ⟨h_2, h_1⟩; exact h_1)

noncomputable def _object_i12 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))))
theorem h_9600 : Litex.Same (_object_i12 (M := M)) (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))))) :=
  (Litex.sameRefl (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
  let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))))))

theorem h_9601 : (by
  have h_9604 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (h_9426 (M := M))
        )
    )
  have h_9605 : ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (h_9415 (M := M))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _object_w35 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w35 _wd_1_1 (h_345 (M := M)) (by
      let _atomic_wd_1_0 := _object_w35
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_object_w35).wd.1 (_object_w35).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (4 : ℂ)) (6 : ℝ) (by norm_num)))) h_9604 h_9605))
    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
    let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    have h_9602 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          )
      )
    have h_9603 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
          )
      )
    have h_9604 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (h_9426 (M := M))
          )
      )
    have h_9605 : ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) :=
      (by
        litex_checked_step =>
          exact (
            (h_9415 (M := M))
          )
      )
    have h_9629 :=
      (Classical.choose (show ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) from h_9605))
    have h_9630 :=
      (Classical.choose_spec (show ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ))) from h_9605))
    have h_9606 : Litex.Same (let _object_w35 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w35 _wd_1_1 (h_345 (M := M)) (by
      let _atomic_wd_1_0 := _object_w35
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_object_w35).wd.1 (_object_w35).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (4 : ℂ)) (6 : ℝ) (by norm_num)))) h_9604 h_9605)) (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
    let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))))) :=
      (by
        litex_checked_step =>
          exact (
            ((h_349 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_9602 (Litex.number (M := M) (4 : ℂ)) h_9603 (Litex.number (M := M) (1 : ℂ)) h_9604 h_9605)
          )
      )
    exact (let _equal_wd_1_0 := (let _object_w35 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) _object_w35 _wd_1_1 (h_345 (M := M)) (by
    let _atomic_wd_1_0 := _object_w35
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_object_w35).wd.1 (_object_w35).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (4 : ℂ)) (6 : ℝ) (by norm_num)))) h_9604 h_9605));
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
  let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))));
  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_9606).trans (Litex.sameRefl _equal_wd_1_1)))))
  )

noncomputable def _object_w39 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)))

theorem h_9711 : (by
  let _equal_wd_1_0 := (_object_w39 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (let _equal_wd_1_0 := (_object_w39 (M := M));
  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (1 : ℂ))])) = (M.number (1 : ℂ)) from by
    have _litex_residual : (M.divValue (M.number (2 : ℂ)) (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = (M.number (1 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (h_9427 (M := M)))));
    (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) ((2 : ℂ) / ((1 : ℂ) + (1 : ℂ))) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_0).val.right).wd.1 ((_equal_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (1 : ℂ))])))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M))))
    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_346 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.number (2 : ℂ)) (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) from rfl))
  ))).trans _litex_residual)))

noncomputable def _object_w40 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)))

theorem h_9856 : (by
  let _equal_wd_1_0 := (_object_w40 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (let _equal_wd_1_0 := (_object_w40 (M := M));
  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (4 : ℂ)), (M.number (1 : ℂ))])) = (M.number (2 : ℂ)) from by
    have _litex_residual : (M.divValue (M.number (4 : ℂ)) (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = (M.number (2 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (h_9427 (M := M)))));
    (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) ((4 : ℂ) / ((1 : ℂ) + (1 : ℂ))) (2 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (4 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_0).val.right).wd.1 ((_equal_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (4 : ℂ)), (M.number (1 : ℂ))])))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M))))
    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_346 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 (M.addValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.number (4 : ℂ)) (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) from rfl))
  ))).trans _litex_residual)))

noncomputable def _object_w42 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))

theorem h_10001 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
  let _wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i5 (M.standard Litex.StandardSetValue.real))), (¬ ((M.addValue _raw_i5 (M.number (1 : ℂ))) = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_345 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (h_9426 (M := M)) (h_9415 (M := M)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (_object_w42 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (congrArg₂ M.addValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (1 : ℂ))])) = (M.number (1 : ℂ)) from (h_9711 (M := M))) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (4 : ℂ)), (M.number (1 : ℂ))])) = (M.number (2 : ℂ)) from (h_9856 (M := M))))

theorem h_10021 : Litex.Same (_object_i12 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (let _equal_wd_2_0 := (_object_w42 (M := M));
  (show Litex.Same (_object_i12 (M := M)) (Litex.number (M := M) (3 : ℂ)) from (Eq.trans (((h_9600 (M := M))).trans (h_10001 (M := M))) (Eq.trans (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((1 : ℂ) + (2 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w42 (M := M))).wd.1 ((_object_w42 (M := M))).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (show @Eq M.Value _ _ from Eq.refl _)))))
end LitexCompiled.file_lean_x2f_examples_x2f_shifted_x5f_guarded_x5f_quotient_x5f_distribution_x2f_statement_x2e_lit
