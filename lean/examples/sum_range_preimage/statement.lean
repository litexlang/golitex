import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sum_x5f_range_x5f_preimage_x2f_statement_x2e_lit

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

theorem _preimage_h_106 : ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (_member_i4 : M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (_member_i5 : M.mem (Litex.denote _value_i5) (M.standard Litex.StandardSetValue.real)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (3 : ℂ))])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)]))) := (by
  obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (by
  have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) ((h_90 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (let _checked_header : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → True := (by
    intro _raw_i2 _raw_i3 h_87 h_88 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_87)
    have h_87 : Litex.In _value_i2 (Litex.R (M := M)) := h_87
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_88)
    have h_88 : Litex.In _value_i3 (Litex.R (M := M)) := h_88
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_89 (M := M)))
  exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True)) _range_signature_0) (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_89 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True)))) (h_89 (M := M)))).mp (by
  let _atomic_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_89 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)
  let _atomic_wd_1_1 := (by
    have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) ((h_90 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
    have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (let _checked_header : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → True := (by
      intro _raw_i2 _raw_i3 h_87 h_88 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_87)
      have h_87 : Litex.In _value_i2 (Litex.R (M := M)) := h_87
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_88)
      have h_88 : Litex.In _value_i3 (Litex.R (M := M)) := h_88
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_89 (M := M)))
    exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True)) _range_signature_0)
  exact (Litex.call2InFnRange _atomic_wd_1_0 _atomic_wd_1_1 (Litex.sameRefl (_object_i1 (M := M)))))
  obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
  have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
  have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _range_domain
  have _range_base_member_0 := (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _range_members (0 : Fin 2))
  have _range_member_0 := _range_base_member_0
  have _range_base_member_1 := (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _range_members (1 : Fin 2))
  have _range_member_1 := _range_base_member_1
  have _range_repack : Litex.denote _range_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (2 : ℂ)))] := by
    apply (Litex.FiniteFunction.reconstruct _range_members).trans
    apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
    funext i
    fin_cases i <;> norm_num [Litex.FiniteFunction.index]
  exact ⟨(Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (1 : ℂ))) (M.member_isSet _range_member_0)), _range_member_0, (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (2 : ℂ))) (M.member_isSet _range_member_1)), _range_member_1, (_range_eq.trans (congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M)))) _range_repack))⟩)

noncomputable def _value_i4 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((_preimage_h_106 (M := M)))

theorem h_104 : (M.mem (Litex.denote (_value_i4 (M := M))) (M.standard Litex.StandardSetValue.real)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((_preimage_h_106 (M := M))))))
      )
  )

noncomputable def _value_i5 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((_preimage_h_106 (M := M)))))))

theorem h_105 : (M.mem (Litex.denote (_value_i5 (M := M))) (M.standard Litex.StandardSetValue.real)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((_preimage_h_106 (M := M))))))))))
      )
  )

theorem h_106 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (3 : ℂ))])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote (_value_i4 (M := M))), (Litex.denote (_value_i5 (M := M)))]))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((_preimage_h_106 (M := M))))))))))
      )
  )

theorem h_107 : (by
  let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (_value_i4 (M := M)) (_value_i5 (M := M)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True)))) (h_89 (M := M))) (h_104 (M := M)) (h_105 (M := M)) True.intro)
  let _equal_wd_1_1 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_89 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        ((h_106 (M := M))).symm
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sum_x5f_range_x5f_preimage_x2f_statement_x2e_lit
