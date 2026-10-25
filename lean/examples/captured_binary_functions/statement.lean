import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_captured_x5f_binary_x5f_functions_x2f_statement_x2e_lit

universe u v7 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → True := (by
    intro _raw_i3 _raw_i4 h_15 h_16 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i4 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) _raw_i2)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ)))))) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) _raw_i2)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ)))))) _raw_i2) (Litex.denote (let _checked_header : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → True := (by
    intro _raw_i3 _raw_i4 h_15 h_16 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i4 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True)))) := (by
    intro _raw_i2 h_14 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
    change (by
      let _atomic_wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i2))) (by
        intro _raw_i5 _raw_i6 h_305 h_306 _
        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_305)
        have h_305 : Litex.In _value_i5 (Litex.R (M := M)) := h_305
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_306)
        have h_306 : Litex.In _value_i6 (Litex.R (M := M)) := h_306
        change (by
          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_305) (M.real_subset_complex _ h_306));
          let _wd_1_1 := _value_i2;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_3_0 := _wd_1_0
            exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_305) (M.real_subset_complex _ h_306))) (M.real_subset_complex _ h_14)))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_305) (M.real_subset_complex _ h_306));
          let _wd_1_1 := _value_i2;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_3_0 := _wd_1_0
            exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_305) (M.real_subset_complex _ h_306))) (M.real_subset_complex _ h_14)))
          exact (Litex.addInR (_atomic_wd_2_0).val.left _value_i2 (Litex.addInR _value_i5 _value_i6 h_305 h_306) h_14))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → True := (by
          intro _raw_i3 _raw_i4 h_566 h_567 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_566)
          have h_566 : Litex.In _value_i3 (Litex.R (M := M)) := h_566
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_567)
          have h_567 : Litex.In _value_i4 (Litex.R (M := M)) := h_567
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True)))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i2))) (by
        intro _raw_i5 _raw_i6 h_305 h_306 _
        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_305)
        have h_305 : Litex.In _value_i5 (Litex.R (M := M)) := h_305
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_306)
        have h_306 : Litex.In _value_i6 (Litex.R (M := M)) := h_306
        change (by
          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_305) (M.real_subset_complex _ h_306));
          let _wd_1_1 := _value_i2;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_3_0 := _wd_1_0
            exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_305) (M.real_subset_complex _ h_306))) (M.real_subset_complex _ h_14)))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_305) (M.real_subset_complex _ h_306));
          let _wd_1_1 := _value_i2;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_3_0 := _wd_1_0
            exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_305) (M.real_subset_complex _ h_306))) (M.real_subset_complex _ h_14)))
          exact (Litex.addInR (_atomic_wd_2_0).val.left _value_i2 (Litex.addInR _value_i5 _value_i6 h_305 h_306) h_14))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → True := (by
          intro _raw_i3 _raw_i4 h_566 h_567 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_566)
          have h_566 : Litex.In _value_i3 (Litex.R (M := M)) := h_566
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_567)
          have h_567 : Litex.In _value_i4 (Litex.R (M := M)) := h_567
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True)))
      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from by exact Litex.formulaFnInFnSet _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote (let _checked_header : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → True := (by
    intro _raw_i3 _raw_i4 h_15 h_16 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i4 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True)))) (Litex.isSet (Litex.R (M := M))) (Litex.isSet (let _checked_header : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → True := (by
    intro _raw_i3 _raw_i4 h_15 h_16 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i4 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_575 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_576 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_579 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_592 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_593 : Litex.In _value_i8 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_594 : Litex.In _value_i9 (Litex.R (M := M))), (by
  let _object_w6 := (let _litex_call_arg_0 := _value_i7;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_575 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_592, True.intro⟩))
  let _object_w7 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (M.addValue (M.addValue _raw_i10 _raw_i11) (Litex.denote _value_i7))) (by
    intro _raw_i10 _raw_i11 h_613 h_614 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_613)
    have h_613 : Litex.In _value_i10 (Litex.R (M := M)) := h_613
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_614)
    have h_614 : Litex.In _value_i11 (Litex.R (M := M)) := h_614
    change (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_613) (M.real_subset_complex _ h_614));
      let _wd_1_1 := _value_i7;
      (Litex.add _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (Litex.addInC _value_i10 _value_i11 (M.real_subset_complex _ h_613) (M.real_subset_complex _ h_614))) (M.real_subset_complex _ h_592)))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_613) (M.real_subset_complex _ h_614));
      let _wd_1_1 := _value_i7;
      (Litex.add _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (Litex.addInC _value_i10 _value_i11 (M.real_subset_complex _ h_613) (M.real_subset_complex _ h_614))) (M.real_subset_complex _ h_592)))
      exact (Litex.addInR (_atomic_wd_1_0).val.left _value_i7 (Litex.addInR _value_i10 _value_i11 h_613 h_614) h_592))))
  let _object_w8 := (by
    let _returned_receiver := (let _litex_call_arg_0 := _value_i7;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_575 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_592, True.intro⟩))
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.callArguments2 _value_i8 _value_i9)) _returned_signature.domain := ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.denote _value_i8) (Litex.denote _value_i9)).mpr ⟨h_593, h_594, True.intro⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.callArguments2 _value_i8 _value_i9) _returned_member _returned_domain)
  let _object_w9 := (let _wd_1_0 := (Litex.add _value_i8 _value_i9 (M.real_subset_complex _ h_593) (M.real_subset_complex _ h_594));
  let _wd_1_1 := _value_i7;
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC _value_i8 _value_i9 (M.real_subset_complex _ h_593) (M.real_subset_complex _ h_594))) (M.real_subset_complex _ h_592)))
  exact (((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w8
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_592 _Host_i8 _rep_i8 _value_i8 h_593 _Host_i9 _rep_i9 _value_i9 h_594
          let _object_w6 := (let _litex_call_arg_0 := _value_i7;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_575 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_592, True.intro⟩))
          let _object_w7 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (M.addValue (M.addValue _raw_i10 _raw_i11) (Litex.denote _value_i7))) (by
            intro _raw_i10 _raw_i11 h_613 h_614 _
            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_613)
            have h_613 : Litex.In _value_i10 (Litex.R (M := M)) := h_613
            let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_614)
            have h_614 : Litex.In _value_i11 (Litex.R (M := M)) := h_614
            change (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_613) (M.real_subset_complex _ h_614));
              let _wd_1_1 := _value_i7;
              (Litex.add _wd_1_0 _wd_1_1 (by
                let _atomic_wd_2_0 := _wd_1_0
                exact (Litex.addInC _value_i10 _value_i11 (M.real_subset_complex _ h_613) (M.real_subset_complex _ h_614))) (M.real_subset_complex _ h_592)))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_613) (M.real_subset_complex _ h_614));
              let _wd_1_1 := _value_i7;
              (Litex.add _wd_1_0 _wd_1_1 (by
                let _atomic_wd_2_0 := _wd_1_0
                exact (Litex.addInC _value_i10 _value_i11 (M.real_subset_complex _ h_613) (M.real_subset_complex _ h_614))) (M.real_subset_complex _ h_592)))
              exact (Litex.addInR (_atomic_wd_1_0).val.left _value_i7 (Litex.addInR _value_i10 _value_i11 h_613 h_614) h_592))))
          have h_577 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (M.addValue (M.addValue _raw_i10 _raw_i11) (Litex.denote _value_i7))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) from by
                    have _litex_residual : (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (M.addValue (M.addValue _raw_i10 _raw_i11) (Litex.denote _value_i7))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) := (let _equal_wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (by
                      intro _raw_i5 _raw_i6 h_1061 h_1062 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1061)
                      have h_1061 : Litex.In _value_i5 (Litex.R (M := M)) := h_1061
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1062)
                      have h_1062 : Litex.In _value_i6 (Litex.R (M := M)) := h_1062
                      change (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_1061) (M.real_subset_complex _ h_1062));
                        let _wd_1_1 := _value_i7;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_1061) (M.real_subset_complex _ h_1062))) (M.real_subset_complex _ h_592)))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_1061) (M.real_subset_complex _ h_1062));
                        let _wd_1_1 := _value_i7;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_1061) (M.real_subset_complex _ h_1062))) (M.real_subset_complex _ h_592)))
                        exact (Litex.addInR (_atomic_wd_1_0).val.left _value_i7 (Litex.addInR _value_i5 _value_i6 h_1061 h_1062) h_592))));
                    let _equal_wd_2_1 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (M.addValue (M.addValue _raw_i10 _raw_i11) (Litex.denote _value_i7))) (by
                      intro _raw_i10 _raw_i11 h_1478 h_1479 _
                      let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1478)
                      have h_1478 : Litex.In _value_i10 (Litex.R (M := M)) := h_1478
                      let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1479)
                      have h_1479 : Litex.In _value_i11 (Litex.R (M := M)) := h_1479
                      change (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_1478) (M.real_subset_complex _ h_1479));
                        let _wd_1_1 := _value_i7;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.addInC _value_i10 _value_i11 (M.real_subset_complex _ h_1478) (M.real_subset_complex _ h_1479))) (M.real_subset_complex _ h_592)))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_1478) (M.real_subset_complex _ h_1479));
                        let _wd_1_1 := _value_i7;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.addInC _value_i10 _value_i11 (M.real_subset_complex _ h_1478) (M.real_subset_complex _ h_1479))) (M.real_subset_complex _ h_592)))
                        exact (Litex.addInR (_atomic_wd_1_0).val.left _value_i7 (Litex.addInR _value_i10 _value_i11 h_1478 h_1479) h_592))));
                    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
                      let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_0
                      let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_1
                      exact (show Litex.Same _left _right from rfl))))
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i7;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → True := (by
                      intro _raw_i3 _raw_i4 h_573 h_574 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_573)
                      have h_573 : Litex.In _value_i3 (Litex.R (M := M)) := h_573
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_574)
                      have h_574 : Litex.In _value_i4 (Litex.R (M := M)) := h_574
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_592 True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_576 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) _raw_i2)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ)))))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))); exact rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w8 := (by
            let _returned_receiver := (let _litex_call_arg_0 := _value_i7;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_575 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_592, True.intro⟩))
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.callArguments2 _value_i8 _value_i9)) _returned_signature.domain := ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.denote _value_i8) (Litex.denote _value_i9)).mpr ⟨h_593, h_594, True.intro⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.callArguments2 _value_i8 _value_i9) _returned_member _returned_domain)
          let _object_w9 := (let _wd_1_0 := (Litex.add _value_i8 _value_i9 (M.real_subset_complex _ h_593) (M.real_subset_complex _ h_594));
          let _wd_1_1 := _value_i7;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i8 _value_i9 (M.real_subset_complex _ h_593) (M.real_subset_complex _ h_594))) (M.real_subset_complex _ h_592)))
          have h_578 : (by
            let _equal_wd_1_0 := _object_w8
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i9)])) = (M.addValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (Litex.denote _value_i7)) from by
                    have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (Litex.denote _value_i7)) = (M.addValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i9)])))).trans (congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i9)])) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) from by
                    let _litex_original := _object_w6
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i7;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → True := (by
                      intro _raw_i3 _raw_i4 h_573 h_574 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_573)
                      have h_573 : Litex.In _value_i3 (Litex.R (M := M)) := h_573
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_574)
                      have h_574 : Litex.In _value_i4 (Litex.R (M := M)) := h_574
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_592 True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_576 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) _raw_i2)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ)))))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))); exact rfl))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i8), (Litex.denote _value_i9)])) = (M.addValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (Litex.denote _value_i7)) from by
                    let _litex_original := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (by
                      intro _raw_i5 _raw_i6 h_2197 h_2198 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_2197)
                      have h_2197 : Litex.In _value_i5 (Litex.R (M := M)) := h_2197
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_2198)
                      have h_2198 : Litex.In _value_i6 (Litex.R (M := M)) := h_2198
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_2197) (M.real_subset_complex _ h_2198));
                        let _wd_2_1 := _value_i7;
                        (Litex.add _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_2197) (M.real_subset_complex _ h_2198))) (M.real_subset_complex _ h_592)))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_2197) (M.real_subset_complex _ h_2198));
                        let _wd_2_1 := _value_i7;
                        (Litex.add _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_2197) (M.real_subset_complex _ h_2198))) (M.real_subset_complex _ h_592)))
                        exact (Litex.addInR (_atomic_wd_1_0).val.left _value_i7 (Litex.addInR _value_i5 _value_i6 h_2197 h_2198) h_592))));
                    let _wd_1_1 := _value_i8;
                    let _wd_1_2 := _value_i9;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_593 h_594 True.intro))
                    let _litex_literal := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (by
                      intro _raw_i5 _raw_i6 h_2630 h_2631 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_2630)
                      have h_2630 : Litex.In _value_i5 (Litex.R (M := M)) := h_2630
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_2631)
                      have h_2631 : Litex.In _value_i6 (Litex.R (M := M)) := h_2631
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_2630) (M.real_subset_complex _ h_2631));
                        let _wd_2_1 := _value_i7;
                        (Litex.add _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_2630) (M.real_subset_complex _ h_2631))) (M.real_subset_complex _ h_592)))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_2630) (M.real_subset_complex _ h_2631));
                        let _wd_2_1 := _value_i7;
                        (Litex.add _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (Litex.addInC _value_i5 _value_i6 (M.real_subset_complex _ h_2630) (M.real_subset_complex _ h_2631))) (M.real_subset_complex _ h_592)))
                        exact (Litex.addInR (_atomic_wd_1_0).val.left _value_i7 (Litex.addInR _value_i5 _value_i6 h_2630 h_2631) h_592))));
                    let _wd_1_1 := _value_i8;
                    let _wd_1_2 := _value_i9;
                    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_593 h_594 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.addValue (M.addValue _raw_i5 _raw_i6) (Litex.denote _value_i7))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i8) (Litex.denote _value_i9)) (Litex.denote _value_i7)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          exact (And.intro h_577 h_578)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_captured_x5f_binary_x5f_functions_x2f_statement_x2e_lit
