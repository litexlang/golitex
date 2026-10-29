import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_definition_x2f_statement_x2e_lit

universe u v1 v3 v4 v5 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_14 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_16 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_19 : Litex.In _value_i4 (Litex.R (M := M))) (h_5 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_20 : Litex.In _value_i5 (Litex.RPos (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_24 : Litex.In _value_i6 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i6 _value_i3 (M.real_subset_complex _ h_24) (M.real_subset_complex _ h_18));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i6 _value_i3 h_24 h_18))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i6 _value_i3 (M.real_subset_complex _ h_24) (M.real_subset_complex _ h_18));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i6 _value_i3 h_24 h_18)))) _value_i5))) (h_12 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_905 : Litex.In _value_i7 (Litex.RPos (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_909 : Litex.In _value_i8 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_913 : Litex.In _value_i9 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i9 _value_i3 (M.real_subset_complex _ h_913) (M.real_subset_complex _ h_18));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i9 _value_i3 h_913 h_18))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i9 _value_i3 (M.real_subset_complex _ h_913) (M.real_subset_complex _ h_18));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i9 _value_i3 h_913 h_18)))) _value_i8)))) (let _wd_1_0 := _value_i1;
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1939 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_1939) (M.real_subset_complex _ h_19));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i10 _value_i4 h_1939 h_19)))) _value_i7));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_2353 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_2353) (M.real_subset_complex _ h_19));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i10 _value_i4 h_2353 h_19)))) _value_i7))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_2353 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_2353) (M.real_subset_complex _ h_19));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i10 _value_i4 h_2353 h_19)))) _value_i7))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_2767 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i12 h_17 h_2767 True.intro) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_16 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_16 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_17)))), (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_16 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
      have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_16 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
      have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_16 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
      have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_17)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_3249 : Litex.In _value_i3 (Litex.R (M := M)) := h_18
  have h_3256 : Litex.In _value_i4 (Litex.R (M := M)) := h_19
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i3 _rep_i3 _value_i3 h_18 _Host_i4 _rep_i4 _value_i4 h_19 h_5 h_12
          have h_3266 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_3265 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
              have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          have h_3267 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_18
                )
            )
          have h_3268 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19
                )
            )
          have h_15 : (by
            have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
              let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_3265 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
              have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_3265 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_3265 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_3266)
              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
              intro x hx
              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
            )
            have h_9771 : Litex.In _value_i3 (Litex.R (M := M)) := h_3267
            have h_9778 : Litex.In _value_i4 (Litex.R (M := M)) := h_3268
            exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                      have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_3266)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_9771 : Litex.In _value_i3 (Litex.R (M := M)) := h_3267
                    have h_9778 : Litex.In _value_i4 (Litex.R (M := M)) := h_3268
                    exact (by
                      let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                      have _member : Litex.In _value_i1 (Litex.fnSet _signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_3266)
                      let _source_domain := (M.standard Litex.StandardSetValue.real)
                      have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
                      have _domain_match : _source_domain = _signature.domain := by
                        apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                        intro x
                        change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                        rw [Litex.SetSemantics.sep_members]
                        exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                      let _domain := Litex.semanticObject _source_domain _domain_set
                      exact Litex.finiteFunctionLimitOfForall .both _value_i1 _value_i3 _value_i4 _domain _function_limit_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_9771 h_9778 (show ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_6532 : Litex.In _value_i14 (Litex.RPos (M := M))), ∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (h_6536 : Litex.In _value_i15 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i15 _value_i3 (M.real_subset_complex _ h_6536) (M.real_subset_complex _ h_3267));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_2_0 := _wd_1_0
                      exact (Litex.subInR _value_i15 _value_i3 h_6536 h_3267))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i15 _value_i3 (M.real_subset_complex _ h_6536) (M.real_subset_complex _ h_3267));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_2_0 := _wd_1_0
                      exact (Litex.subInR _value_i15 _value_i3 h_6536 h_3267)))) _value_i14)) from (by
                      intro _Host_i14 _rep_i14 _value_i14 h_6532
                      have h_6533 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inRPos_positive _value_i14 h_6532)
                            )
                        )
                      have h_6534 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_6533)
                            )
                        )
                      have h_6535 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_6533) _litex_zero.symm)
                            )
                        )
                      exact (h_5 _value_i14 h_6532)
                    )) (show ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_7427 : Litex.In _value_i16 (Litex.RPos (M := M))), ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_7431 : Litex.In _value_i17 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_7435 : Litex.In _value_i18 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i18 _value_i3 (M.real_subset_complex _ h_7435) (M.real_subset_complex _ h_3267));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_2_0 := _wd_1_0
                      exact (Litex.subInR _value_i18 _value_i3 h_7435 h_3267))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i18 _value_i3 (M.real_subset_complex _ h_7435) (M.real_subset_complex _ h_3267));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_2_0 := _wd_1_0
                      exact (Litex.subInR _value_i18 _value_i3 h_7435 h_3267)))) _value_i17)))) (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_8461 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i4 (M.real_subset_complex _ h_8461) (M.real_subset_complex _ h_3268));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_2_0 := _wd_2_0
                      exact (Litex.subInR _value_i19 _value_i4 h_8461 h_3268)))) _value_i16));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_8875 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i4 (M.real_subset_complex _ h_8875) (M.real_subset_complex _ h_3268));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_3_0 := _wd_2_0
                        exact (Litex.subInR _value_i19 _value_i4 h_8875 h_3268)))) _value_i16))
                      exact Litex.IsSet _atomic_wd_2_0) := (by
                      let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_8875 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i4 (M.real_subset_complex _ h_8875) (M.real_subset_complex _ h_3268));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_3_0 := _wd_2_0
                        exact (Litex.subInR _value_i19 _value_i4 h_8875 h_3268)))) _value_i16))
                      exact (Litex.isSet _atomic_wd_2_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9289 : Litex.In _value_i20 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i20 h_3266 h_9289 True.intro) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_3266))) from (by
                      intro _Host_i16 _rep_i16 _value_i16 h_7427
                      have h_7428 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inRPos_positive _value_i16 h_7427)
                            )
                        )
                      have h_7429 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_7428)
                            )
                        )
                      have h_7430 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_7428) _litex_zero.symm)
                            )
                        )
                      exact (h_12 _value_i16 h_7427)
                    ))
                    ))
                )
            )
          exact h_15
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_definition_x2f_statement_x2e_lit
