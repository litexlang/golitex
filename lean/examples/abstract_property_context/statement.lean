import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_property_x5f_context_x2f_statement_x2e_lit

universe u v1 v9 v10 v11 v12 v14
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_1 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M)))

variable (abstract_prop_2 : (Fin 1 → M.Value) → Prop)

noncomputable def _object_i4 (abstract_prop_2 : (Fin 1 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (abstract_prop_2 ![_raw_i5])) (fun (_raw_i5 : M.Value) => (M.addValue _raw_i5 (Litex.denote _value_i1))) (by
  intro _raw_i5 h_33 h_3
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_33)
  have h_33 : Litex.In _value_i5 (Litex.R (M := M)) := h_33
  have h_3 : (abstract_prop_2 ![(Litex.denote _value_i5)]) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (abstract_prop_2 ![_raw_i5])
            exact h_3)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i5 _value_i1 (M.real_subset_complex _ h_33) (M.real_subset_complex _ h_2))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i5 _value_i1 (M.real_subset_complex _ h_33) (M.real_subset_complex _ h_2))
    exact (Litex.addInR _value_i5 _value_i1 h_33 h_2))))
theorem h_106 (abstract_prop_2 : (Fin 1 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.In (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.fnSet ((_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
      )
  )
theorem h_107 (abstract_prop_2 : (Fin 1 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.Same (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
      )
  )

variable (abstract_prop_4 : (Fin 1 → M.Value) → Prop)

theorem h_108 (abstract_prop_2 : (Fin 1 → M.Value) → Prop) (abstract_prop_4 : (Fin 1 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_109 : Litex.In _value_i9 (Litex.R (M := M)))

theorem h_112 (abstract_prop_2 : (Fin 1 → M.Value) → Prop) (abstract_prop_4 : (Fin 1 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_109 : Litex.In _value_i9 (Litex.R (M := M))) : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_125 : Litex.In _value_i10 (Litex.R (M := M))) (h_110 : (abstract_prop_2 ![(Litex.denote _value_i10)])), (by
  let _object_w4 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (abstract_prop_2 ![_raw_i5])) (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) _value_i10 (h_106 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) h_125 h_110)
  let _object_w5 := (Litex.add _value_i10 _value_i1 (M.real_subset_complex _ h_125) (M.real_subset_complex _ h_2))
  exact (by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_125 h_110
          let _object_w4 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (abstract_prop_2 ![_raw_i5])) (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) _value_i10 (h_106 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) h_125 h_110)
          let _object_w5 := (Litex.add _value_i10 _value_i1 (M.real_subset_complex _ h_125) (M.real_subset_complex _ h_2))
          have h_111 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) (Litex.denote _value_i10)) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i1)) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i1)) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i1)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) (Litex.denote _value_i10)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) (Litex.denote _value_i10)) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i1)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2);
                    let _wd_1_1 := _value_i10;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (abstract_prop_2 ![_raw_i5])) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_125 h_110))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_107 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (abstract_prop_2 ![_raw_i5])) (fun (_raw_i5 : M.Value) => (M.addValue _raw_i5 (Litex.denote _value_i1))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (abstract_prop_2 ![_raw_i5])) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.addValue _raw_i5 (Litex.denote _value_i1))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i1)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_111
        )
      )
  )

theorem h_321 (abstract_prop_2 : (Fin 1 → M.Value) → Prop) (abstract_prop_4 : (Fin 1 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_109 : Litex.In _value_i9 (Litex.R (M := M))) : ∀ {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_335 : Litex.In _value_i11 (Litex.R (M := M))) (h_319 : (abstract_prop_4 ![(Litex.denote _value_i11)])), (abstract_prop_4 ![(Litex.denote _value_i11)]) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i11 _rep_i11 _value_i11 h_335 h_319
          have h_320 : (abstract_prop_4 ![(Litex.denote _value_i11)]) :=
            (by
              litex_checked_step =>
                exact (
                  h_319
                )
            )
          exact h_320
        )
      )
  )

def prop_8 (abstract_prop_2 : (Fin 1 → M.Value) → Prop) (abstract_prop_4 : (Fin 1 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_109 : Litex.In _value_i9 (Litex.R (M := M))) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) : Prop :=
  ∃ (h_340 : Litex.In _value_i12 (Litex.R (M := M))), ∃ (h_338 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i12), (abstract_prop_2 ![(Litex.denote _value_i12)])

theorem h_358 (abstract_prop_2 : (Fin 1 → M.Value) → Prop) (abstract_prop_4 : (Fin 1 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_109 : Litex.In _value_i9 (Litex.R (M := M))) : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_371 : Litex.In _value_i14 (Litex.R (M := M))) (h_355 : ((prop_8 (M := M) abstract_prop_2 abstract_prop_4 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i9 := _Host_i9) (_rep_i9 := _rep_i9) _value_i9 h_109) _value_i14)), (((abstract_prop_2 ![(Litex.denote _value_i14)])) ∧ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_371 h_355
          have h_372 :=
            (Classical.choose (show ((prop_8 (M := M) abstract_prop_2 abstract_prop_4 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i9 := _Host_i9) (_rep_i9 := _rep_i9) _value_i9 h_109) _value_i14) from h_355))
          have h_373 :=
            (Classical.choose (Classical.choose_spec (show ((prop_8 (M := M) abstract_prop_2 abstract_prop_4 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i9 := _Host_i9) (_rep_i9 := _rep_i9) _value_i9 h_109) _value_i14) from h_355)))
          have h_374 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_8 (M := M) abstract_prop_2 abstract_prop_4 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i9 := _Host_i9) (_rep_i9 := _rep_i9) _value_i9 h_109) _value_i14) from h_355)))
          have h_356 : (abstract_prop_2 ![(Litex.denote _value_i14)]) :=
            (by
              litex_checked_step =>
                exact (
                  h_374
                )
            )
          have h_357 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  h_373
                )
            )
          exact (And.intro h_356 h_357)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_property_x5f_context_x2f_statement_x2e_lit
