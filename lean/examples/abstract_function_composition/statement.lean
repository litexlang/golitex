import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_function_x5f_composition_x2f_statement_x2e_lit

universe u v1 v3 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_52 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_51 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
    have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_54 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_53 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
    have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_55 : Litex.In _value_i5 (Litex.R (M := M))), (by
  let _object_w31 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i6))) (by
    intro _raw_i6 h_69 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_69)
    have h_69 : Litex.In _value_i6 (Litex.R (M := M)) := h_69
    change (by
      let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w19 h_52 (by
        let _atomic_wd_2_0 := _object_w19
        exact (by
          let _litex_return_call := _object_w19
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w19 h_52 (by
        let _atomic_wd_2_0 := _object_w19
        exact (by
          let _litex_return_call := _object_w19
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_51 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_53 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
      have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_54) (by
    have _composition_checked : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i6) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
    intro _raw_i6 h_69 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_69)
    have h_69 : Litex.In _value_i6 (Litex.R (M := M)) := h_69
    let _composition_call := (let _object_w18 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w18 h_52 (by
    let _atomic_wd_1_0 := _object_w18
    exact (by
      let _litex_return_call := _object_w18
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_51 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) _value_i5 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i6))) (by
    intro _raw_i6 h_69 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_69)
    have h_69 : Litex.In _value_i6 (Litex.R (M := M)) := h_69
    change (by
      let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w19 h_52 (by
        let _atomic_wd_2_0 := _object_w19
        exact (by
          let _litex_return_call := _object_w19
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w19 h_52 (by
        let _atomic_wd_2_0 := _object_w19
        exact (by
          let _litex_return_call := _object_w19
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_51 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_53 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
      have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_54) (by
    have _composition_checked : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i6) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
    intro _raw_i6 h_69 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_69)
    have h_69 : Litex.In _value_i6 (Litex.R (M := M)) := h_69
    let _composition_call := (let _object_w18 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w18 h_52 (by
    let _atomic_wd_1_0 := _object_w18
    exact (by
      let _litex_return_call := _object_w18
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_51 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_51 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_53 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
      have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_54)) h_55 True.intro)
  let _object_w32 := (let _object_w20 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i5 h_54 h_55 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w20 h_52 (by
    let _atomic_wd_1_0 := _object_w20
    exact (by
      let _litex_return_call := _object_w20
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact (by
    let _equal_wd_1_0 := _object_w31
    let _equal_wd_1_1 := _object_w32
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_52 _Host_i3 _rep_i3 _value_i3 h_54 _Host_i5 _rep_i5 _value_i5 h_55
          let _object_w31 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i6))) (by
            intro _raw_i6 h_69 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_69)
            have h_69 : Litex.In _value_i6 (Litex.R (M := M)) := h_69
            change (by
              let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w19 h_52 (by
                let _atomic_wd_2_0 := _object_w19
                exact (by
                  let _litex_return_call := _object_w19
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w19 h_52 (by
                let _atomic_wd_2_0 := _object_w19
                exact (by
                  let _litex_return_call := _object_w19
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_51 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
              have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_53 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
              have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_54) (by
            have _composition_checked : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i6) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i6 h_69 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_69)
            have h_69 : Litex.In _value_i6 (Litex.R (M := M)) := h_69
            let _composition_call := (let _object_w18 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w18 h_52 (by
            let _atomic_wd_1_0 := _object_w18
            exact (by
              let _litex_return_call := _object_w18
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_51 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
              have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) _value_i5 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i6))) (by
            intro _raw_i6 h_69 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_69)
            have h_69 : Litex.In _value_i6 (Litex.R (M := M)) := h_69
            change (by
              let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w19 h_52 (by
                let _atomic_wd_2_0 := _object_w19
                exact (by
                  let _litex_return_call := _object_w19
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w19 h_52 (by
                let _atomic_wd_2_0 := _object_w19
                exact (by
                  let _litex_return_call := _object_w19
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_51 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
              have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_53 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
              have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_54) (by
            have _composition_checked : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i6) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i6 h_69 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_69)
            have h_69 : Litex.In _value_i6 (Litex.R (M := M)) := h_69
            let _composition_call := (let _object_w18 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i6 h_54 h_69 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w18 h_52 (by
            let _atomic_wd_1_0 := _object_w18
            exact (by
              let _litex_return_call := _object_w18
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_51 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
              have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_51 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
              have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_53 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
              have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_54)) h_55 True.intro)
          let _object_w32 := (let _object_w20 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i5 h_54 h_55 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w20 h_52 (by
            let _atomic_wd_1_0 := _object_w20
            exact (by
              let _litex_return_call := _object_w20
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w31
            let _equal_wd_1_1 := _object_w32
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w31;
                  let _equal_wd_1_1 := _object_w32;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_equal_wd_1_0).val.function) (Litex.denote _value_i5)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i5))) from by
                    have _litex_residual : (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i5))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i5))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_equal_wd_1_0).val.function) (Litex.denote _value_i5)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_equal_wd_1_0).val.function) (Litex.denote _value_i5)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i5))) from by
                    have _composition_head := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _value_i5)) (show (Litex.denote (_equal_wd_1_0).val.function) = Litex.denote (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10))) (by
                    intro _raw_i10 h_1331 _
                    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1331)
                    have h_1331 : Litex.In _value_i10 (Litex.R (M := M)) := h_1331
                    change (by
                      let _atomic_wd_1_0 := (let _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_54 h_1331 True.intro);
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w28 h_52 (by
                        let _atomic_wd_2_0 := _object_w28
                        exact (by
                          let _litex_return_call := _object_w28
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                    exact (by
                      let _atomic_wd_1_0 := (let _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_54 h_1331 True.intro);
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w28 h_52 (by
                        let _atomic_wd_2_0 := _object_w28
                        exact (by
                          let _litex_return_call := _object_w28
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
                  Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_51 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
                      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_53 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
                      have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_54) (by
                    have _composition_checked : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
                    intro _raw_i10 h_1331 _
                    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1331)
                    have h_1331 : Litex.In _value_i10 (Litex.R (M := M)) := h_1331
                    let _composition_call := (let _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_54 h_1331 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w27 h_52 (by
                    let _atomic_wd_1_0 := _object_w27
                    exact (by
                      let _litex_return_call := _object_w27
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_51 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
                      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52))
                    intro _composition_input _preimage_domain
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
                    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                    exact _composition_checked _composition_input _preimage_members True.intro)) from (show @Eq M.Value _ _ from Eq.refl _))
                    exact _composition_head.trans (Litex.composeCall (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10))) (by
                    intro _raw_i10 h_1331 _
                    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1331)
                    have h_1331 : Litex.In _value_i10 (Litex.R (M := M)) := h_1331
                    change (by
                      let _atomic_wd_1_0 := (let _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_54 h_1331 True.intro);
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w28 h_52 (by
                        let _atomic_wd_2_0 := _object_w28
                        exact (by
                          let _litex_return_call := _object_w28
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                    exact (by
                      let _atomic_wd_1_0 := (let _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_54 h_1331 True.intro);
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w28 h_52 (by
                        let _atomic_wd_2_0 := _object_w28
                        exact (by
                          let _litex_return_call := _object_w28
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
                  Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_51 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
                      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_53 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
                      have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_54) (by
                    have _composition_checked : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
                    intro _raw_i10 h_1331 _
                    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1331)
                    have h_1331 : Litex.In _value_i10 (Litex.R (M := M)) := h_1331
                    let _composition_call := (let _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_54 h_1331 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w27 h_52 (by
                    let _atomic_wd_1_0 := _object_w27
                    exact (by
                      let _litex_return_call := _object_w27
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_51 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
                      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52))
                    intro _composition_input _preimage_domain
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
                    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                    exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_51 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_51)
                      have h_51 : Litex.In _value_i2 (Litex.R (M := M)) := h_51
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_52) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_53 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_53)
                      have h_53 : Litex.In _value_i4 (Litex.R (M := M)) := h_53
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_54) (Litex.denote _value_i5) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (Litex.denote _value_i5)).mpr ⟨h_55, True.intro⟩))))).trans _litex_residual)))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_function_x5f_composition_x2f_statement_x2e_lit
