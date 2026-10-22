import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_function_x5f_expansion_x2f_statement_x2e_lit

universe u v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.powerSet (Litex.R (M := M)))) (Litex.isSet (Litex.R (M := M))) (Litex.isSet (Litex.powerSet (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (_raw_i3 = _raw_i2)))) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (_raw_i3 = _raw_i2)))) _raw_i2) (Litex.denote (Litex.powerSet (Litex.R (M := M)))) := (by
    intro _raw_i2 h_15 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i2 (Litex.R (M := M)) := h_15
    change (by
      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Same _value_i3 _value_i2))
      let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Same _value_i3 _value_i2))
      let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
      exact ((Litex.inPowerSet_iff _atomic_wd_1_0 (Litex.R (M := M))).mpr (by
        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_26 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Same _value_i3 _value_i2))
        exact (by
          let _set := _atomic_wd_2_0
          exact Litex.setBuilderSubset _set.val.bound _set.val.predicate)))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.powerSet (Litex.R (M := M)))) (Litex.isSet (Litex.R (M := M))) (Litex.isSet (Litex.powerSet (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_28 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_29 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

theorem h_30 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_31 : Litex.In _value_i4 (Litex.R (M := M)))

noncomputable def _object_w6 {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_31 : Litex.In _value_i4 (Litex.R (M := M))) := (let _litex_call_arg_0 := _value_i4;
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_28 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_31, True.intro⟩))

noncomputable def _object_w7 {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_31 : Litex.In _value_i4 (Litex.R (M := M))) := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_41 : Litex.In _value_i5 (Litex.R (M := M))) => Litex.Same _value_i5 _value_i4))

theorem h_33 {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_31 : Litex.In _value_i4 (Litex.R (M := M))) : (by
  let _equal_wd_1_0 := (_object_w6 (M := M) (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_31)
  let _equal_wd_1_1 := (_object_w7 (M := M) (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_31)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i5 : M.Value) => ∃ (_ : M.mem _raw_i5 (M.standard Litex.StandardSetValue.real)), (_raw_i5 = (Litex.denote _value_i4)))) from by
    have _litex_residual : (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (_raw_i3 = (Litex.denote _value_i4)))) = (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i5 : M.Value) => ∃ (_ : M.mem _raw_i5 (M.standard Litex.StandardSetValue.real)), (_raw_i5 = (Litex.denote _value_i4)))) := (let _equal_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_84 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Same _value_i3 _value_i4));
    let _equal_wd_2_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_85 : Litex.In _value_i5 (Litex.R (M := M))) => Litex.Same _value_i5 _value_i4));
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from rfl)))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (_raw_i3 = (Litex.denote _value_i4)))) from by
    let _litex_original := (let _litex_call_arg_0 := _value_i4;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_28 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_31, True.intro⟩))
    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
  let _wd_1_1 := _value_i4;
  (let _litex_call_arg_0 := _wd_1_1;
  Litex.callOnDomain (Litex.R (M := M)) (Litex.powerSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_31 True.intro))
    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_29 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (_raw_i3 = _raw_i2)))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (_raw_i3 = (Litex.denote _value_i4)))); exact rfl))
  ))).trans _litex_residual)
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_function_x5f_expansion_x2f_statement_x2e_lit
