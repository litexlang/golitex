import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_control_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_7 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_9 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_10 : Litex.In _value_i4 (Litex.RPos (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_7 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_7 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_7 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_8)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_16 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
  exact Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i3)), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_23 : Litex.In _value_i5 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_24 : Litex.In _value_i6 (Litex.R (M := M))) => Litex.Lt _value_i5 _value_i6)) (let _wd_1_0 := _value_i1;
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_65 : Litex.In _value_i7 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i7 _value_i3 (M.real_subset_complex _ h_65) (M.real_subset_complex _ h_9));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i7 _value_i3 h_65 h_9)))) _value_i4));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_412 : Litex.In _value_i7 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i7 _value_i3 (M.real_subset_complex _ h_412) (M.real_subset_complex _ h_9));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i7 _value_i3 h_412 h_9)))) _value_i4))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_412 : Litex.In _value_i7 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i7 _value_i3 (M.real_subset_complex _ h_412) (M.real_subset_complex _ h_9));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i7 _value_i3 h_412 h_9)))) _value_i4))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_759 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i9 h_8 h_759 True.intro) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_7 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_7 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_8))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i3 _rep_i3 _value_i3 h_9 _Host_i4 _rep_i4 _value_i4 h_10 h_1
          have h_11 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i4 h_10)
                )
            )
          have h_12 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 h_11)
                )
            )
          have h_13 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 h_11) _litex_zero.symm)
                )
            )
          have h_1172 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_1171 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1171)
              have h_1171 : Litex.In _value_i2 (Litex.R (M := M)) := h_1171
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_1173 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_1174 : Litex.In _value_i4 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_1175 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i4 h_1174)
                )
            )
          have h_1176 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 h_1175)
                )
            )
          have h_1177 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 h_1175) _litex_zero.symm)
                )
            )
          have h_1197 : ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_2978 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_2979 : Litex.In _value_i11 (Litex.R (M := M))) => Litex.Lt _value_i10 _value_i11)) (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_3020 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 _value_i3 (M.real_subset_complex _ h_3020) (M.real_subset_complex _ h_1173));
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR _value_i12 _value_i3 h_3020 h_1173)))) _value_i4));
          (by
            have _preimage_target : (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_3367 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 _value_i3 (M.real_subset_complex _ h_3367) (M.real_subset_complex _ h_1173));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i12 _value_i3 h_3367 h_1173)))) _value_i4))
            exact Litex.IsSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_3367 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 _value_i3 (M.real_subset_complex _ h_3367) (M.real_subset_complex _ h_1173));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i12 _value_i3 h_3367 h_1173)))) _value_i4))
            exact (Litex.isSet _atomic_wd_1_0))
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_3714 : Litex.In _value_i16 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i16 h_1172 h_3714 True.intro) _wd_1_1))
            exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_1171 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1171)
              have h_1171 : Litex.In _value_i2 (Litex.R (M := M)) := h_1171
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_1171 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1171)
              have h_1171 : Litex.In _value_i2 (Litex.R (M := M)) := h_1171
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1172))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_1189 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_1171 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1171)
                          have h_1171 : Litex.In _value_i2 (Litex.R (M := M)) := h_1171
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_1171 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1171)
                                  have h_1171 : Litex.In _value_i2 (Litex.R (M := M)) := h_1171
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_1172)
                          )
                      )
                    have h_1190 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_1191 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1190
                          )
                      )
                    have h_1192 : Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_1193 : Litex.In _value_i4 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1174
                          )
                      )
                    have h_1226 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i4 h_1193)
                          )
                      )
                    have h_1227 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 h_1226)
                          )
                      )
                    have h_1228 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 h_1226) _litex_zero.symm)
                          )
                      )
                    exact (show ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_1229 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_1230 : Litex.In _value_i11 (Litex.R (M := M))) => Litex.Lt _value_i10 _value_i11)) (let _wd_1_0 := _value_i1;
                  let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_1284 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 _value_i3 (M.real_subset_complex _ h_1284) (M.real_subset_complex _ h_1173));
                  (Litex.abs _wd_2_0 (by
                    let _atomic_wd_1_0 := _wd_2_0
                    exact (Litex.subInR _value_i12 _value_i3 h_1284 h_1173)))) _value_i4));
                  (by
                    have _preimage_target : (by
                    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_1823 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 _value_i3 (M.real_subset_complex _ h_1823) (M.real_subset_complex _ h_1173));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_2_0 := _wd_2_0
                      exact (Litex.subInR _value_i12 _value_i3 h_1823 h_1173)))) _value_i4))
                    exact Litex.IsSet _atomic_wd_1_0) := (by
                    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_1823 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 _value_i3 (M.real_subset_complex _ h_1823) (M.real_subset_complex _ h_1173));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_2_0 := _wd_2_0
                      exact (Litex.subInR _value_i12 _value_i3 h_1823 h_1173)))) _value_i4))
                    exact (Litex.isSet _atomic_wd_1_0))
                    let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_2362 : Litex.In _value_i15 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i15 h_1189 h_2362 True.intro) _wd_1_1))
                    exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_1171 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1171)
                      have h_1171 : Litex.In _value_i2 (Litex.R (M := M)) := h_1171
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_1171 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1171)
                      have h_1171 : Litex.In _value_i2 (Litex.R (M := M)) := h_1171
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1189))) from (by
                    let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_1171 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1171)
                      have h_1171 : Litex.In _value_i2 (Litex.R (M := M)) := h_1171
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                    have _member : Litex.In _value_i1 (Litex.fnSet _signature) := h_1189
                    let _source_domain := (M.standard Litex.StandardSetValue.real)
                    have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
                    have _domain_match : _source_domain = _signature.domain := by
                      apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                      intro x
                      change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                      rw [Litex.SetSemantics.sep_members]
                      exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                    let _domain := Litex.semanticObject _source_domain _domain_set
                    have _control_real_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := by
                      refine ⟨_signature, _member, ?_, h_1191⟩
                      intro x hx
                      exact h_1190 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    obtain ⟨_limit_threshold, _limit_threshold_member, _limit_control⟩ := Litex.infiniteFunctionLimitControl .positive _value_i1 _value_i3 _domain _control_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_1192 _value_i4 h_1193
                    refine ⟨_limit_threshold, _limit_threshold_member, ?_⟩
                    exact _limit_control
                  ))
                  )
                )
            )
          exact h_1197
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_control_x5f_by_x5f_theorem_x2f_statement_x2e_lit
