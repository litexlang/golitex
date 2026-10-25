import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_function_x5f_guard_x2f_statement_x2e_lit

universe u v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

variable (abstract_prop_1 : (Fin 1 → M.Value) → Prop)

noncomputable def _object_i3 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (abstract_prop_1 ![_raw_i4])) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (by
  intro _raw_i4 h_31 h_1
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_31)
  have h_31 : Litex.In _value_i4 (Litex.R (M := M)) := h_31
  have h_1 : (abstract_prop_1 ![(Litex.denote _value_i4)]) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (abstract_prop_1 ![_raw_i4])
            exact h_1)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_31) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_31) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i4 (Litex.number (M := M) (1 : ℂ)) h_31 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_70 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) : Litex.In (_object_i3 (M := M) abstract_prop_1) (Litex.fnSet ((_object_i3 (M := M) abstract_prop_1)).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M) abstract_prop_1))
      )
  )
theorem h_71 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) : Litex.Same (_object_i3 (M := M) abstract_prop_1) (_object_i3 (M := M) abstract_prop_1) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M) abstract_prop_1))
      )
  )

theorem h_74 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_87 : Litex.In _value_i6 (Litex.R (M := M))) (h_72 : (abstract_prop_1 ![(Litex.denote _value_i6)])), (by
  let _object_w7 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (abstract_prop_1 ![_raw_i4])) (_object_i3 (M := M) abstract_prop_1) _value_i6 (h_70 (M := M) abstract_prop_1) h_87 h_72)
  let _object_w8 := (Litex.add _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_87) (Litex.numberInC (M := M) (1 : ℂ)))
  exact (by
    let _equal_wd_1_0 := _object_w7
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_87 h_72
          let _object_w7 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (abstract_prop_1 ![_raw_i4])) (_object_i3 (M := M) abstract_prop_1) _value_i6 (h_70 (M := M) abstract_prop_1) h_87 h_72)
          let _object_w8 := (Litex.add _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_87) (Litex.numberInC (M := M) (1 : ℂ)))
          have h_73 : (by
            let _equal_wd_1_0 := _object_w7
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w7;
                  let _equal_wd_1_1 := _object_w8;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M) abstract_prop_1)) (Litex.denote _value_i6)) = (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) = (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M) abstract_prop_1)) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M) abstract_prop_1)) (Litex.denote _value_i6)) = (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M) abstract_prop_1);
                    let _wd_1_1 := _value_i6;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (abstract_prop_1 ![_raw_i4])) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_87 h_72))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_71 (M := M) abstract_prop_1) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (abstract_prop_1 ![_raw_i4])) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (abstract_prop_1 ![_raw_i4])) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_73
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_function_x5f_guard_x2f_statement_x2e_lit
