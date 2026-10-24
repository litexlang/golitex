import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_shift_x5f_range_x5f_preimage_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_53 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_54 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w5 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)

noncomputable def _object_w6 := (by
  have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_54 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
  have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
    intro _raw_i2 h_52 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_52)
    have h_52 : Litex.In _value_i2 (Litex.R (M := M)) := h_52
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_53 (M := M)))
  exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) _range_signature_0)

theorem h_55 : (by
  let _atomic_wd_1_0 := (_object_w5 (M := M))
  let _atomic_wd_1_1 := (_object_w6 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w5 (M := M))
          let _atomic_wd_1_1 := (_object_w6 (M := M))
          exact (Litex.callInFnRange _atomic_wd_1_0 _atomic_wd_1_1 (Litex.sameRefl (_object_i1 (M := M)))))
      )
  )

theorem h_65 : Litex.In (_object_w5 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.fnRangeInOutput (_object_w6 (M := M)) (_object_w5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) (h_53 (M := M))) (h_55 (M := M)))
      )
  )

theorem _preimage_h_74 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (_member_i3 : M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) := (by
  obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (_object_w6 (M := M)) (_object_w5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) (h_53 (M := M)))).mp (by
  let _atomic_wd_1_0 := (_object_w5 (M := M))
  let _atomic_wd_1_1 := (_object_w6 (M := M))
  exact (h_55 (M := M)))
  obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _).mp _range_domain
  have _range_base_member_0 := _range_members
  have _range_member_0 := _range_base_member_0
  exact ⟨(Litex.semanticObject (Litex.denote _range_input) (M.member_isSet _range_member_0)), _range_member_0, _range_eq⟩)

noncomputable def _value_i3 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((_preimage_h_74 (M := M)))

theorem h_73 : (M.mem (Litex.denote (_value_i3 (M := M))) (M.standard Litex.StandardSetValue.real)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((_preimage_h_74 (M := M))))))
      )
  )

theorem h_74 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_value_i3 (M := M))))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((_preimage_h_74 (M := M))))))
      )
  )

theorem h_75 : Litex.In (_value_i3 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (h_73 (M := M))
      )
  )

theorem h_86 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (_value_i3 (M := M)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) (h_53 (M := M))) (h_73 (M := M)) True.intro)
  let _equal_wd_1_1 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        ((h_74 (M := M))).symm
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_shift_x5f_range_x5f_preimage_x2f_statement_x2e_lit
