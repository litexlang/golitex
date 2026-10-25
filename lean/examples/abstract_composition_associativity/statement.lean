import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_composition_x5f_associativity_x2f_statement_x2e_lit

universe u v1 v3 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_58 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_57 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
    have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_60 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_59 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
    have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_62 : Litex.In _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
    intro _raw_i6 h_61 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
    have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))), (by
  let _object_w53 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True) (fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.compositionValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i3)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i9))) (by
    intro _raw_i9 h_652 _
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_652)
    have h_652 : Litex.In _value_i9 (Litex.R (M := M)) := h_652
    change (by
      let _atomic_wd_1_0 := (let _object_w37 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i9 h_62 h_652 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11))) (by
        intro _raw_i11 h_1102 _
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
        have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
        change (by
          let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
            let _atomic_wd_3_0 := _object_w36
            exact (by
              let _litex_return_call := _object_w36
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
            let _atomic_wd_3_0 := _object_w36
            exact (by
              let _litex_return_call := _object_w36
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
      Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
        have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
        intro _raw_i11 h_1102 _
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
        have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
        let _composition_call := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w35 h_58 (by
        let _atomic_wd_2_0 := _object_w35
        exact (by
          let _litex_return_call := _object_w35
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
        intro _composition_input _preimage_domain
        obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
        have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
        exact _composition_checked _composition_input _preimage_members True.intro)) _object_w37 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11))) (by
        intro _raw_i11 h_1102 _
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
        have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
        change (by
          let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
            let _atomic_wd_3_0 := _object_w36
            exact (by
              let _litex_return_call := _object_w36
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
            let _atomic_wd_3_0 := _object_w36
            exact (by
              let _litex_return_call := _object_w36
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
      Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
        have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
        intro _raw_i11 h_1102 _
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
        have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
        let _composition_call := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w35 h_58 (by
        let _atomic_wd_2_0 := _object_w35
        exact (by
          let _litex_return_call := _object_w35
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
        intro _composition_input _preimage_domain
        obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
        have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
        exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) (by
        let _atomic_wd_2_0 := _object_w37
        exact (by
          let _litex_return_call := _object_w37
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w37 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i9 h_62 h_652 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11))) (by
        intro _raw_i11 h_1102 _
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
        have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
        change (by
          let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
            let _atomic_wd_3_0 := _object_w36
            exact (by
              let _litex_return_call := _object_w36
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
            let _atomic_wd_3_0 := _object_w36
            exact (by
              let _litex_return_call := _object_w36
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
      Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
        have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
        intro _raw_i11 h_1102 _
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
        have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
        let _composition_call := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w35 h_58 (by
        let _atomic_wd_2_0 := _object_w35
        exact (by
          let _litex_return_call := _object_w35
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
        intro _composition_input _preimage_domain
        obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
        have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
        exact _composition_checked _composition_input _preimage_members True.intro)) _object_w37 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11))) (by
        intro _raw_i11 h_1102 _
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
        have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
        change (by
          let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
            let _atomic_wd_3_0 := _object_w36
            exact (by
              let _litex_return_call := _object_w36
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
            let _atomic_wd_3_0 := _object_w36
            exact (by
              let _litex_return_call := _object_w36
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
      Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
        have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
        intro _raw_i11 h_1102 _
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
        have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
        let _composition_call := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w35 h_58 (by
        let _atomic_wd_2_0 := _object_w35
        exact (by
          let _litex_return_call := _object_w35
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
        intro _composition_input _preimage_domain
        obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
        have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
        exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) (by
        let _atomic_wd_2_0 := _object_w37
        exact (by
          let _litex_return_call := _object_w37
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))).output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.denote (_atomic_wd_1_0).val.argument) (Litex.composeInFnSet (_atomic_wd_1_0).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_57 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
          have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (Litex.denote (_atomic_wd_1_0).val.argument)).mpr ⟨(by
        let _atomic_wd_2_0 := (_atomic_wd_1_0).val.argument
        exact (by
          let _litex_return_call := (_atomic_wd_1_0).val.argument
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))), True.intro⟩)))));
  Litex.compose (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i7))) (by
    intro _raw_i7 h_76 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_76)
    have h_76 : Litex.In _value_i7 (Litex.R (M := M)) := h_76
    change (by
      let _atomic_wd_1_0 := (let _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i7 h_60 h_76 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w27 h_58 (by
        let _atomic_wd_2_0 := _object_w27
        exact (by
          let _litex_return_call := _object_w27
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i7 h_60 h_76 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w27 h_58 (by
        let _atomic_wd_2_0 := _object_w27
        exact (by
          let _litex_return_call := _object_w27
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
    have _composition_checked : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i7) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
    intro _raw_i7 h_76 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_76)
    have h_76 : Litex.In _value_i7 (Litex.R (M := M)) := h_76
    let _composition_call := (let _object_w26 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i7 h_60 h_76 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w26 h_58 (by
    let _atomic_wd_1_0 := _object_w26
    exact (by
      let _litex_return_call := _object_w26
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i8))) (by
    intro _raw_i8 h_364 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_364)
    have h_364 : Litex.In _value_i8 (Litex.R (M := M)) := h_364
    change (by
      let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w30 h_58 (by
        let _atomic_wd_2_0 := _object_w30
        exact (by
          let _litex_return_call := _object_w30
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w30 h_58 (by
        let _atomic_wd_2_0 := _object_w30
        exact (by
          let _litex_return_call := _object_w30
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
    have _composition_checked : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i8) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
    intro _raw_i8 h_364 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_364)
    have h_364 : Litex.In _value_i8 (Litex.R (M := M)) := h_364
    let _composition_call := (let _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w29 h_58 (by
    let _atomic_wd_1_0 := _object_w29
    exact (by
      let _litex_return_call := _object_w29
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
      intro _raw_i6 h_61 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
      have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
    have _composition_checked : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i9) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))).domain := (by
    intro _raw_i9 h_652 _
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_652)
    have h_652 : Litex.In _value_i9 (Litex.R (M := M)) := h_652
    let _composition_call := (let _object_w34 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i9 h_62 h_652 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10))) (by
    intro _raw_i10 h_666 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_666)
    have h_666 : Litex.In _value_i10 (Litex.R (M := M)) := h_666
    change (by
      let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w33 h_58 (by
        let _atomic_wd_2_0 := _object_w33
        exact (by
          let _litex_return_call := _object_w33
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w33 h_58 (by
        let _atomic_wd_2_0 := _object_w33
        exact (by
          let _litex_return_call := _object_w33
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
    have _composition_checked : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
    intro _raw_i10 h_666 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_666)
    have h_666 : Litex.In _value_i10 (Litex.R (M := M)) := h_666
    let _composition_call := (let _object_w32 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w32 h_58 (by
    let _atomic_wd_1_0 := _object_w32
    exact (by
      let _litex_return_call := _object_w32
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) _object_w34 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10))) (by
    intro _raw_i10 h_666 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_666)
    have h_666 : Litex.In _value_i10 (Litex.R (M := M)) := h_666
    change (by
      let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w33 h_58 (by
        let _atomic_wd_2_0 := _object_w33
        exact (by
          let _litex_return_call := _object_w33
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w33 h_58 (by
        let _atomic_wd_2_0 := _object_w33
        exact (by
          let _litex_return_call := _object_w33
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
    have _composition_checked : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
    intro _raw_i10 h_666 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_666)
    have h_666 : Litex.In _value_i10 (Litex.R (M := M)) := h_666
    let _composition_call := (let _object_w32 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w32 h_58 (by
    let _atomic_wd_1_0 := _object_w32
    exact (by
      let _litex_return_call := _object_w32
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) (by
    let _atomic_wd_1_0 := _object_w34
    exact (by
      let _litex_return_call := _object_w34
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True)) (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i8))) (by
    intro _raw_i8 h_364 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_364)
    have h_364 : Litex.In _value_i8 (Litex.R (M := M)) := h_364
    change (by
      let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w30 h_58 (by
        let _atomic_wd_2_0 := _object_w30
        exact (by
          let _litex_return_call := _object_w30
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w30 h_58 (by
        let _atomic_wd_2_0 := _object_w30
        exact (by
          let _litex_return_call := _object_w30
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
    have _composition_checked : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i8) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
    intro _raw_i8 h_364 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_364)
    have h_364 : Litex.In _value_i8 (Litex.R (M := M)) := h_364
    let _composition_call := (let _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w29 h_58 (by
    let _atomic_wd_1_0 := _object_w29
    exact (by
      let _litex_return_call := _object_w29
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro))
  let _object_w54 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) => True) (fun (_raw_i15 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.compositionValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i5)) _raw_i15))) (by
    intro _raw_i15 h_2198 _
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_2198)
    have h_2198 : Litex.In _value_i15 (Litex.R (M := M)) := h_2198
    change (by
      let _atomic_wd_1_0 := (let _object_w50 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18))) (by
        intro _raw_i18 h_2646 _
        let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
        have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
        change (by
          let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
            let _atomic_wd_3_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
            let _atomic_wd_3_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
      Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
          intro _raw_i6 h_61 _
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
          have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
        have _composition_checked : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
        intro _raw_i18 h_2646 _
        let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
        have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
        let _composition_call := (let _object_w48 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w48 h_60 (by
        let _atomic_wd_2_0 := _object_w48
        exact (by
          let _litex_return_call := _object_w48
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
        intro _composition_input _preimage_domain
        obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
        have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
        exact _composition_checked _composition_input _preimage_members True.intro)) _value_i15 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18))) (by
        intro _raw_i18 h_2646 _
        let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
        have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
        change (by
          let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
            let _atomic_wd_3_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
            let _atomic_wd_3_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
      Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
          intro _raw_i6 h_61 _
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
          have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
        have _composition_checked : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
        intro _raw_i18 h_2646 _
        let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
        have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
        let _composition_call := (let _object_w48 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w48 h_60 (by
        let _atomic_wd_2_0 := _object_w48
        exact (by
          let _litex_return_call := _object_w48
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
        intro _composition_input _preimage_domain
        obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
        have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
        exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
          intro _raw_i6 h_61 _
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
          have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) h_2198 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w50 h_58 (by
        let _atomic_wd_2_0 := _object_w50
        exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True))).output (Litex.denote (_object_w50).val.function) (Litex.denote _value_i15) (Litex.composeInFnSet (_object_w50).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
            intro _raw_i4 h_59 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
            have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
            intro _raw_i6 h_61 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
            have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True) (Litex.denote _value_i15)).mpr ⟨h_2198, True.intro⟩))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w50 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18))) (by
        intro _raw_i18 h_2646 _
        let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
        have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
        change (by
          let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
            let _atomic_wd_3_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
            let _atomic_wd_3_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
      Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
          intro _raw_i6 h_61 _
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
          have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
        have _composition_checked : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
        intro _raw_i18 h_2646 _
        let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
        have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
        let _composition_call := (let _object_w48 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w48 h_60 (by
        let _atomic_wd_2_0 := _object_w48
        exact (by
          let _litex_return_call := _object_w48
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
        intro _composition_input _preimage_domain
        obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
        have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
        exact _composition_checked _composition_input _preimage_members True.intro)) _value_i15 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18))) (by
        intro _raw_i18 h_2646 _
        let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
        have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
        change (by
          let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
            let _atomic_wd_3_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
            let _atomic_wd_3_0 := _object_w49
            exact (by
              let _litex_return_call := _object_w49
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
      Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
          intro _raw_i6 h_61 _
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
          have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
        have _composition_checked : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
        intro _raw_i18 h_2646 _
        let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
        have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
        let _composition_call := (let _object_w48 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w48 h_60 (by
        let _atomic_wd_2_0 := _object_w48
        exact (by
          let _litex_return_call := _object_w48
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
        intro _composition_input _preimage_domain
        obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
        have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
        exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_59 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
          have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
          intro _raw_i6 h_61 _
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
          have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) h_2198 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w50 h_58 (by
        let _atomic_wd_2_0 := _object_w50
        exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True))).output (Litex.denote (_object_w50).val.function) (Litex.denote _value_i15) (Litex.composeInFnSet (_object_w50).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
            intro _raw_i4 h_59 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
            have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
            intro _raw_i6 h_61 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
            have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True) (Litex.denote _value_i15)).mpr ⟨h_2198, True.intro⟩))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i1 (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i13 : M.Value) => True) (fun (_raw_i13 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i13))) (by
    intro _raw_i13 h_1622 _
    let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_1622)
    have h_1622 : Litex.In _value_i13 (Litex.R (M := M)) := h_1622
    change (by
      let _atomic_wd_1_0 := (let _object_w40 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i13 h_62 h_1622 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w40 h_60 (by
        let _atomic_wd_2_0 := _object_w40
        exact (by
          let _litex_return_call := _object_w40
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w40 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i13 h_62 h_1622 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w40 h_60 (by
        let _atomic_wd_2_0 := _object_w40
        exact (by
          let _litex_return_call := _object_w40
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
      intro _raw_i6 h_61 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
      have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
    have _composition_checked : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i13) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
    intro _raw_i13 h_1622 _
    let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_1622)
    have h_1622 : Litex.In _value_i13 (Litex.R (M := M)) := h_1622
    let _composition_call := (let _object_w39 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i13 h_62 h_1622 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w39 h_60 (by
    let _atomic_wd_1_0 := _object_w39
    exact (by
      let _litex_return_call := _object_w39
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (fun (_raw_i14 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i14))) (by
    intro _raw_i14 h_1910 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1910)
    have h_1910 : Litex.In _value_i14 (Litex.R (M := M)) := h_1910
    change (by
      let _atomic_wd_1_0 := (let _object_w43 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i14 h_62 h_1910 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w43 h_60 (by
        let _atomic_wd_2_0 := _object_w43
        exact (by
          let _litex_return_call := _object_w43
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w43 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i14 h_62 h_1910 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w43 h_60 (by
        let _atomic_wd_2_0 := _object_w43
        exact (by
          let _litex_return_call := _object_w43
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
      intro _raw_i6 h_61 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
      have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
    have _composition_checked : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i14) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
    intro _raw_i14 h_1910 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1910)
    have h_1910 : Litex.In _value_i14 (Litex.R (M := M)) := h_1910
    let _composition_call := (let _object_w42 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i14 h_62 h_1910 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w42 h_60 (by
    let _atomic_wd_1_0 := _object_w42
    exact (by
      let _litex_return_call := _object_w42
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
      intro _raw_i6 h_61 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
      have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) (by
    have _composition_checked : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.compositionValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i5)) _raw_i15) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
    intro _raw_i15 h_2198 _
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_2198)
    have h_2198 : Litex.In _value_i15 (Litex.R (M := M)) := h_2198
    let _composition_call := (let _object_w47 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i16 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i16))) (by
    intro _raw_i16 h_2212 _
    let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2212)
    have h_2212 : Litex.In _value_i16 (Litex.R (M := M)) := h_2212
    change (by
      let _atomic_wd_1_0 := (let _object_w46 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w46 h_60 (by
        let _atomic_wd_2_0 := _object_w46
        exact (by
          let _litex_return_call := _object_w46
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w46 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w46 h_60 (by
        let _atomic_wd_2_0 := _object_w46
        exact (by
          let _litex_return_call := _object_w46
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
      intro _raw_i6 h_61 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
      have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
    have _composition_checked : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i16) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
    intro _raw_i16 h_2212 _
    let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2212)
    have h_2212 : Litex.In _value_i16 (Litex.R (M := M)) := h_2212
    let _composition_call := (let _object_w45 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w45 h_60 (by
    let _atomic_wd_1_0 := _object_w45
    exact (by
      let _litex_return_call := _object_w45
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) _value_i15 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i16))) (by
    intro _raw_i16 h_2212 _
    let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2212)
    have h_2212 : Litex.In _value_i16 (Litex.R (M := M)) := h_2212
    change (by
      let _atomic_wd_1_0 := (let _object_w46 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w46 h_60 (by
        let _atomic_wd_2_0 := _object_w46
        exact (by
          let _litex_return_call := _object_w46
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w46 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w46 h_60 (by
        let _atomic_wd_2_0 := _object_w46
        exact (by
          let _litex_return_call := _object_w46
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
      intro _raw_i6 h_61 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
      have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
    have _composition_checked : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i16) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
    intro _raw_i16 h_2212 _
    let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2212)
    have h_2212 : Litex.In _value_i16 (Litex.R (M := M)) := h_2212
    let _composition_call := (let _object_w45 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w45 h_60 (by
    let _atomic_wd_1_0 := _object_w45
    exact (by
      let _litex_return_call := _object_w45
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_59 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
      have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
      intro _raw_i6 h_61 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
      have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) h_2198 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w47 h_58 (by
    let _atomic_wd_1_0 := _object_w47
    exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i17 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i17 : M.Value) => True))).output (Litex.denote (_object_w47).val.function) (Litex.denote _value_i15) (Litex.composeInFnSet (_object_w47).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
        intro _raw_i4 h_59 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
        have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
        exact True.intro);
      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
        intro _raw_i6 h_61 _
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
        have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
        exact True.intro);
      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i17 : M.Value) => True) (Litex.denote _value_i15)).mpr ⟨h_2198, True.intro⟩))) True.intro))
    exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_57 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
      have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
    intro _composition_input _preimage_domain
    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input) _).mp _preimage_domain
    have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
    exact _composition_checked _composition_input _preimage_members True.intro))
  exact (by
    let _equal_wd_1_0 := _object_w53
    let _equal_wd_1_1 := _object_w54
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_58 _Host_i3 _rep_i3 _value_i3 h_60 _Host_i5 _rep_i5 _value_i5 h_62
          let _object_w53 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True) (fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.compositionValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i3)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i9))) (by
            intro _raw_i9 h_652 _
            let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_652)
            have h_652 : Litex.In _value_i9 (Litex.R (M := M)) := h_652
            change (by
              let _atomic_wd_1_0 := (let _object_w37 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i9 h_62 h_652 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11))) (by
                intro _raw_i11 h_1102 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
                have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
                change (by
                  let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
                    let _atomic_wd_3_0 := _object_w36
                    exact (by
                      let _litex_return_call := _object_w36
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
                    let _atomic_wd_3_0 := _object_w36
                    exact (by
                      let _litex_return_call := _object_w36
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
              Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
                have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
                intro _raw_i11 h_1102 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
                have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
                let _composition_call := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w35 h_58 (by
                let _atomic_wd_2_0 := _object_w35
                exact (by
                  let _litex_return_call := _object_w35
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
                intro _composition_input _preimage_domain
                obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
                have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                exact _composition_checked _composition_input _preimage_members True.intro)) _object_w37 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11))) (by
                intro _raw_i11 h_1102 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
                have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
                change (by
                  let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
                    let _atomic_wd_3_0 := _object_w36
                    exact (by
                      let _litex_return_call := _object_w36
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
                    let _atomic_wd_3_0 := _object_w36
                    exact (by
                      let _litex_return_call := _object_w36
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
              Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
                have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
                intro _raw_i11 h_1102 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
                have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
                let _composition_call := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w35 h_58 (by
                let _atomic_wd_2_0 := _object_w35
                exact (by
                  let _litex_return_call := _object_w35
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
                intro _composition_input _preimage_domain
                obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
                have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) (by
                let _atomic_wd_2_0 := _object_w37
                exact (by
                  let _litex_return_call := _object_w37
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w37 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i9 h_62 h_652 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11))) (by
                intro _raw_i11 h_1102 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
                have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
                change (by
                  let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
                    let _atomic_wd_3_0 := _object_w36
                    exact (by
                      let _litex_return_call := _object_w36
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
                    let _atomic_wd_3_0 := _object_w36
                    exact (by
                      let _litex_return_call := _object_w36
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
              Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
                have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
                intro _raw_i11 h_1102 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
                have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
                let _composition_call := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w35 h_58 (by
                let _atomic_wd_2_0 := _object_w35
                exact (by
                  let _litex_return_call := _object_w35
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
                intro _composition_input _preimage_domain
                obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
                have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                exact _composition_checked _composition_input _preimage_members True.intro)) _object_w37 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11))) (by
                intro _raw_i11 h_1102 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
                have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
                change (by
                  let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
                    let _atomic_wd_3_0 := _object_w36
                    exact (by
                      let _litex_return_call := _object_w36
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w36 h_58 (by
                    let _atomic_wd_3_0 := _object_w36
                    exact (by
                      let _litex_return_call := _object_w36
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
              Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
                have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
                intro _raw_i11 h_1102 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1102)
                have h_1102 : Litex.In _value_i11 (Litex.R (M := M)) := h_1102
                let _composition_call := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_60 h_1102 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w35 h_58 (by
                let _atomic_wd_2_0 := _object_w35
                exact (by
                  let _litex_return_call := _object_w35
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
                intro _composition_input _preimage_domain
                obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
                have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) (by
                let _atomic_wd_2_0 := _object_w37
                exact (by
                  let _litex_return_call := _object_w37
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))).output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.denote (_atomic_wd_1_0).val.argument) (Litex.composeInFnSet (_atomic_wd_1_0).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                  intro _raw_i2 h_57 _
                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                  have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (Litex.denote (_atomic_wd_1_0).val.argument)).mpr ⟨(by
                let _atomic_wd_2_0 := (_atomic_wd_1_0).val.argument
                exact (by
                  let _litex_return_call := (_atomic_wd_1_0).val.argument
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))), True.intro⟩)))));
          Litex.compose (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i7))) (by
            intro _raw_i7 h_76 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_76)
            have h_76 : Litex.In _value_i7 (Litex.R (M := M)) := h_76
            change (by
              let _atomic_wd_1_0 := (let _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i7 h_60 h_76 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w27 h_58 (by
                let _atomic_wd_2_0 := _object_w27
                exact (by
                  let _litex_return_call := _object_w27
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i7 h_60 h_76 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w27 h_58 (by
                let _atomic_wd_2_0 := _object_w27
                exact (by
                  let _litex_return_call := _object_w27
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
            have _composition_checked : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i7) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i7 h_76 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_76)
            have h_76 : Litex.In _value_i7 (Litex.R (M := M)) := h_76
            let _composition_call := (let _object_w26 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i7 h_60 h_76 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w26 h_58 (by
            let _atomic_wd_1_0 := _object_w26
            exact (by
              let _litex_return_call := _object_w26
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i8))) (by
            intro _raw_i8 h_364 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_364)
            have h_364 : Litex.In _value_i8 (Litex.R (M := M)) := h_364
            change (by
              let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w30 h_58 (by
                let _atomic_wd_2_0 := _object_w30
                exact (by
                  let _litex_return_call := _object_w30
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w30 h_58 (by
                let _atomic_wd_2_0 := _object_w30
                exact (by
                  let _litex_return_call := _object_w30
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
            have _composition_checked : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i8) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i8 h_364 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_364)
            have h_364 : Litex.In _value_i8 (Litex.R (M := M)) := h_364
            let _composition_call := (let _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w29 h_58 (by
            let _atomic_wd_1_0 := _object_w29
            exact (by
              let _litex_return_call := _object_w29
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
              intro _raw_i6 h_61 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
              have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
            have _composition_checked : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i9) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))).domain := (by
            intro _raw_i9 h_652 _
            let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_652)
            have h_652 : Litex.In _value_i9 (Litex.R (M := M)) := h_652
            let _composition_call := (let _object_w34 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i9 h_62 h_652 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10))) (by
            intro _raw_i10 h_666 _
            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_666)
            have h_666 : Litex.In _value_i10 (Litex.R (M := M)) := h_666
            change (by
              let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w33 h_58 (by
                let _atomic_wd_2_0 := _object_w33
                exact (by
                  let _litex_return_call := _object_w33
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w33 h_58 (by
                let _atomic_wd_2_0 := _object_w33
                exact (by
                  let _litex_return_call := _object_w33
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
            have _composition_checked : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i10 h_666 _
            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_666)
            have h_666 : Litex.In _value_i10 (Litex.R (M := M)) := h_666
            let _composition_call := (let _object_w32 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w32 h_58 (by
            let _atomic_wd_1_0 := _object_w32
            exact (by
              let _litex_return_call := _object_w32
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) _object_w34 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10))) (by
            intro _raw_i10 h_666 _
            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_666)
            have h_666 : Litex.In _value_i10 (Litex.R (M := M)) := h_666
            change (by
              let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w33 h_58 (by
                let _atomic_wd_2_0 := _object_w33
                exact (by
                  let _litex_return_call := _object_w33
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w33 h_58 (by
                let _atomic_wd_2_0 := _object_w33
                exact (by
                  let _litex_return_call := _object_w33
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
            have _composition_checked : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i10) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i10 h_666 _
            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_666)
            have h_666 : Litex.In _value_i10 (Litex.R (M := M)) := h_666
            let _composition_call := (let _object_w32 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_60 h_666 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w32 h_58 (by
            let _atomic_wd_1_0 := _object_w32
            exact (by
              let _litex_return_call := _object_w32
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)) (by
            let _atomic_wd_1_0 := _object_w34
            exact (by
              let _litex_return_call := _object_w34
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True)) (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i8))) (by
            intro _raw_i8 h_364 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_364)
            have h_364 : Litex.In _value_i8 (Litex.R (M := M)) := h_364
            change (by
              let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w30 h_58 (by
                let _atomic_wd_2_0 := _object_w30
                exact (by
                  let _litex_return_call := _object_w30
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w30 h_58 (by
                let _atomic_wd_2_0 := _object_w30
                exact (by
                  let _litex_return_call := _object_w30
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i1 _value_i3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (by
            have _composition_checked : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i8) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i8 h_364 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_364)
            have h_364 : Litex.In _value_i8 (Litex.R (M := M)) := h_364
            let _composition_call := (let _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_60 h_364 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w29 h_58 (by
            let _atomic_wd_1_0 := _object_w29
            exact (by
              let _litex_return_call := _object_w29
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60)))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro))
          let _object_w54 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) => True) (fun (_raw_i15 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.compositionValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i5)) _raw_i15))) (by
            intro _raw_i15 h_2198 _
            let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_2198)
            have h_2198 : Litex.In _value_i15 (Litex.R (M := M)) := h_2198
            change (by
              let _atomic_wd_1_0 := (let _object_w50 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18))) (by
                intro _raw_i18 h_2646 _
                let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
                have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
                change (by
                  let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
                    let _atomic_wd_3_0 := _object_w49
                    exact (by
                      let _litex_return_call := _object_w49
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
                    let _atomic_wd_3_0 := _object_w49
                    exact (by
                      let _litex_return_call := _object_w49
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
              Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                  intro _raw_i6 h_61 _
                  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
                  have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
                have _composition_checked : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
                intro _raw_i18 h_2646 _
                let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
                have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
                let _composition_call := (let _object_w48 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w48 h_60 (by
                let _atomic_wd_2_0 := _object_w48
                exact (by
                  let _litex_return_call := _object_w48
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
                intro _composition_input _preimage_domain
                obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
                have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                exact _composition_checked _composition_input _preimage_members True.intro)) _value_i15 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18))) (by
                intro _raw_i18 h_2646 _
                let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
                have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
                change (by
                  let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
                    let _atomic_wd_3_0 := _object_w49
                    exact (by
                      let _litex_return_call := _object_w49
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
                    let _atomic_wd_3_0 := _object_w49
                    exact (by
                      let _litex_return_call := _object_w49
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
              Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                  intro _raw_i6 h_61 _
                  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
                  have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
                have _composition_checked : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
                intro _raw_i18 h_2646 _
                let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
                have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
                let _composition_call := (let _object_w48 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w48 h_60 (by
                let _atomic_wd_2_0 := _object_w48
                exact (by
                  let _litex_return_call := _object_w48
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
                intro _composition_input _preimage_domain
                obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
                have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                  intro _raw_i6 h_61 _
                  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
                  have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) h_2198 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w50 h_58 (by
                let _atomic_wd_2_0 := _object_w50
                exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True))).output (Litex.denote (_object_w50).val.function) (Litex.denote _value_i15) (Litex.composeInFnSet (_object_w50).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                    intro _raw_i4 h_59 _
                    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                    have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                    exact True.intro);
                  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                    intro _raw_i6 h_61 _
                    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
                    have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
                    exact True.intro);
                  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True) (Litex.denote _value_i15)).mpr ⟨h_2198, True.intro⟩))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w50 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18))) (by
                intro _raw_i18 h_2646 _
                let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
                have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
                change (by
                  let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
                    let _atomic_wd_3_0 := _object_w49
                    exact (by
                      let _litex_return_call := _object_w49
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
                    let _atomic_wd_3_0 := _object_w49
                    exact (by
                      let _litex_return_call := _object_w49
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
              Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                  intro _raw_i6 h_61 _
                  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
                  have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
                have _composition_checked : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
                intro _raw_i18 h_2646 _
                let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
                have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
                let _composition_call := (let _object_w48 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w48 h_60 (by
                let _atomic_wd_2_0 := _object_w48
                exact (by
                  let _litex_return_call := _object_w48
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
                intro _composition_input _preimage_domain
                obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
                have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                exact _composition_checked _composition_input _preimage_members True.intro)) _value_i15 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18))) (by
                intro _raw_i18 h_2646 _
                let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
                have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
                change (by
                  let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
                    let _atomic_wd_3_0 := _object_w49
                    exact (by
                      let _litex_return_call := _object_w49
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _object_w49 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w49 h_60 (by
                    let _atomic_wd_3_0 := _object_w49
                    exact (by
                      let _litex_return_call := _object_w49
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
              Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                  intro _raw_i6 h_61 _
                  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
                  have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
                have _composition_checked : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i18) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
                intro _raw_i18 h_2646 _
                let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2646)
                have h_2646 : Litex.In _value_i18 (Litex.R (M := M)) := h_2646
                let _composition_call := (let _object_w48 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i18 h_62 h_2646 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w48 h_60 (by
                let _atomic_wd_2_0 := _object_w48
                exact (by
                  let _litex_return_call := _object_w48
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
                intro _composition_input _preimage_domain
                obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
                have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_59 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                  have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                  intro _raw_i6 h_61 _
                  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
                  have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
                  exact True.intro);
                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) h_2198 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w50 h_58 (by
                let _atomic_wd_2_0 := _object_w50
                exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True))).output (Litex.denote (_object_w50).val.function) (Litex.denote _value_i15) (Litex.composeInFnSet (_object_w50).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                    intro _raw_i4 h_59 _
                    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                    have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                    exact True.intro);
                  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                    intro _raw_i6 h_61 _
                    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
                    have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
                    exact True.intro);
                  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True) (Litex.denote _value_i15)).mpr ⟨h_2198, True.intro⟩))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i1 (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i13 : M.Value) => True) (fun (_raw_i13 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i13))) (by
            intro _raw_i13 h_1622 _
            let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_1622)
            have h_1622 : Litex.In _value_i13 (Litex.R (M := M)) := h_1622
            change (by
              let _atomic_wd_1_0 := (let _object_w40 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i13 h_62 h_1622 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w40 h_60 (by
                let _atomic_wd_2_0 := _object_w40
                exact (by
                  let _litex_return_call := _object_w40
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w40 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i13 h_62 h_1622 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w40 h_60 (by
                let _atomic_wd_2_0 := _object_w40
                exact (by
                  let _litex_return_call := _object_w40
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
              intro _raw_i6 h_61 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
              have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
            have _composition_checked : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i13) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
            intro _raw_i13 h_1622 _
            let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_1622)
            have h_1622 : Litex.In _value_i13 (Litex.R (M := M)) := h_1622
            let _composition_call := (let _object_w39 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i13 h_62 h_1622 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w39 h_60 (by
            let _atomic_wd_1_0 := _object_w39
            exact (by
              let _litex_return_call := _object_w39
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58) (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (fun (_raw_i14 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i14))) (by
            intro _raw_i14 h_1910 _
            let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1910)
            have h_1910 : Litex.In _value_i14 (Litex.R (M := M)) := h_1910
            change (by
              let _atomic_wd_1_0 := (let _object_w43 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i14 h_62 h_1910 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w43 h_60 (by
                let _atomic_wd_2_0 := _object_w43
                exact (by
                  let _litex_return_call := _object_w43
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w43 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i14 h_62 h_1910 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w43 h_60 (by
                let _atomic_wd_2_0 := _object_w43
                exact (by
                  let _litex_return_call := _object_w43
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
              intro _raw_i6 h_61 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
              have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
            have _composition_checked : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i14) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
            intro _raw_i14 h_1910 _
            let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1910)
            have h_1910 : Litex.In _value_i14 (Litex.R (M := M)) := h_1910
            let _composition_call := (let _object_w42 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i14 h_62 h_1910 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w42 h_60 (by
            let _atomic_wd_1_0 := _object_w42
            exact (by
              let _litex_return_call := _object_w42
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
              intro _raw_i6 h_61 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
              have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) (by
            have _composition_checked : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.compositionValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i5)) _raw_i15) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i15 h_2198 _
            let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_2198)
            have h_2198 : Litex.In _value_i15 (Litex.R (M := M)) := h_2198
            let _composition_call := (let _object_w47 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i16 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i16))) (by
            intro _raw_i16 h_2212 _
            let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2212)
            have h_2212 : Litex.In _value_i16 (Litex.R (M := M)) := h_2212
            change (by
              let _atomic_wd_1_0 := (let _object_w46 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w46 h_60 (by
                let _atomic_wd_2_0 := _object_w46
                exact (by
                  let _litex_return_call := _object_w46
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w46 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w46 h_60 (by
                let _atomic_wd_2_0 := _object_w46
                exact (by
                  let _litex_return_call := _object_w46
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
              intro _raw_i6 h_61 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
              have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
            have _composition_checked : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i16) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
            intro _raw_i16 h_2212 _
            let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2212)
            have h_2212 : Litex.In _value_i16 (Litex.R (M := M)) := h_2212
            let _composition_call := (let _object_w45 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w45 h_60 (by
            let _atomic_wd_1_0 := _object_w45
            exact (by
              let _litex_return_call := _object_w45
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) _value_i15 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i16))) (by
            intro _raw_i16 h_2212 _
            let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2212)
            have h_2212 : Litex.In _value_i16 (Litex.R (M := M)) := h_2212
            change (by
              let _atomic_wd_1_0 := (let _object_w46 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w46 h_60 (by
                let _atomic_wd_2_0 := _object_w46
                exact (by
                  let _litex_return_call := _object_w46
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w46 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w46 h_60 (by
                let _atomic_wd_2_0 := _object_w46
                exact (by
                  let _litex_return_call := _object_w46
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose _value_i3 _value_i5 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
              intro _raw_i6 h_61 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
              have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62) (by
            have _composition_checked : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) _raw_i16) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
            intro _raw_i16 h_2212 _
            let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2212)
            have h_2212 : Litex.In _value_i16 (Litex.R (M := M)) := h_2212
            let _composition_call := (let _object_w45 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _value_i5 _value_i16 h_62 h_2212 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _object_w45 h_60 (by
            let _atomic_wd_1_0 := _object_w45
            exact (by
              let _litex_return_call := _object_w45
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_59 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
              have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
              intro _raw_i6 h_61 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
              have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) h_2198 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _object_w47 h_58 (by
            let _atomic_wd_1_0 := _object_w47
            exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i17 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i17 : M.Value) => True))).output (Litex.denote (_object_w47).val.function) (Litex.denote _value_i15) (Litex.composeInFnSet (_object_w47).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)) (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_59 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_59)
                have h_59 : Litex.In _value_i4 (Litex.R (M := M)) := h_59
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_60) (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_61 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_61)
                have h_61 : Litex.In _value_i6 (Litex.R (M := M)) := h_61
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_62)) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i17 : M.Value) => True) (Litex.denote _value_i15)).mpr ⟨h_2198, True.intro⟩))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_57 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
              have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_58))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input) _).mp _preimage_domain
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members True.intro))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w53
            let _equal_wd_1_1 := _object_w54
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w53;
                  let _equal_wd_1_1 := _object_w54;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.FunctionSemantics.composition_associative (Litex.composeSpec (_equal_wd_1_0).val.outer) (Litex.composeSpec (_equal_wd_1_1).val.inner) (Litex.composeSpec _equal_wd_1_0) (Litex.composeSpec _equal_wd_1_1))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_composition_x5f_associativity_x2f_statement_x2e_lit
