import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_domain_x5f_preimages_x2f_statement_x2e_lit

universe u v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _positive_i2
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_14, _positive_i2⟩)
  have h_15 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i2 h_14)
        )
    )
  have h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_15)
        )
    )
  have h_17 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_15) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.inRPos_real _value_i2 h_14) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_75 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_76 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w7 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_75 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2)

theorem h_77 : (by
  let _equal_wd_1_0 := (_object_w7 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w7 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.number (3 : ℂ)) from by
          have _litex_residual : (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = (M.number (3 : ℂ)) := (let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_76 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w16 := (by
  let _preimage_builder := (Litex.setBuilder (Litex.RPos (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_113 : Litex.In _value_i3 (Litex.RPos (M := M))) => Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) _value_i3 (h_75 (M := M)) (Litex.inRPos_real _value_i3 h_113) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i3)).mp h_113).2) (Litex.number (M := M) (3 : ℂ))))
  exact Litex.preimage (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))

theorem h_111 : (by
  let _atomic_wd_1_1 := (_object_w16 (M := M))
  exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w16 (M := M))
          exact (by
            let _preimage := _atomic_wd_1_1
            let _preimage_builder := (Litex.setBuilder (Litex.RPos (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_127 : Litex.In _value_i4 (Litex.RPos (M := M))) => Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) _value_i4 (h_75 (M := M)) (Litex.inRPos_real _value_i4 h_127) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i4)).mp h_127).2) (Litex.number (M := M) (3 : ℂ))))
            have _preimage_same : (Litex.denote (Litex.number (M := M) (2 : ℂ))) = (Litex.denote (Litex.number (M := M) (2 : ℂ))) := rfl
            exact (Litex.preimageMembers _preimage (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))).domain) _preimage_same) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))), ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2⟩), Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote _preimage.val.function) x = Litex.denote _preimage.val.target) _preimage_same) (h_77 (M := M))⟩))
      )
  )

theorem h_142 : (M.mem (M.number (2 : ℂ)) (Litex.positiveReal (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w16 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w16 (M := M)) (_object_w16 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (show @Eq M.Value _ _ from Eq.refl _) (h_111 (M := M)))
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _litex_input) _).mp _preimage_domain
          have _preimage_positive_i2 := _preimage_guard
          have _preimage_base : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.RPos (M := M))) := ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨_preimage_members, _preimage_positive_i2⟩)
          exact _preimage_base)
      )
  )

theorem h_146 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_159 : Litex.In _value_i6 (_object_w16 (M := M))), ((Litex.In _value_i6 (Litex.RPos (M := M))) ∧ ((by
  let _equal_wd_1_0 := (by
    have _preimage_domain := ((Litex.preimageMembers (_object_w16 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i6)).mp (Litex.inOfSame _value_i6 _value_i6 (_object_w16 (M := M)) (_object_w16 (M := M)) (Litex.sameRefl _value_i6) (show @Eq M.Value _ _ from Eq.refl _) h_159)).1
    exact Litex.callOn (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (_object_i1 (M := M)) _value_i6 (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) _preimage_domain)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_159
          have h_161 : (M.mem (Litex.denote _value_i6) (Litex.positiveReal (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w16 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i6)).mp (Litex.inOfSame _value_i6 _value_i6 (_object_w16 (M := M)) (_object_w16 (M := M)) (Litex.sameRefl _value_i6) (show @Eq M.Value _ _ from Eq.refl _) h_159)
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _litex_input) _).mp _preimage_domain
                    have _preimage_positive_i2 := _preimage_guard
                    have _preimage_base : M.mem (Litex.denote _value_i6) (Litex.denote (Litex.RPos (M := M))) := ((Litex.positiveReal_members (M := M) (Litex.denote _value_i6)).mpr ⟨_preimage_members, _preimage_positive_i2⟩)
                    exact _preimage_base)
                )
            )
          have h_162 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.number (3 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w16 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i6)).mp (Litex.inOfSame _value_i6 _value_i6 (_object_w16 (M := M)) (_object_w16 (M := M)) (Litex.sameRefl _value_i6) (show @Eq M.Value _ _ from Eq.refl _) h_159)
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _litex_input) _).mp _preimage_domain
                    have _preimage_positive_i2 := _preimage_guard
                    have _preimage_base : M.mem (Litex.denote _value_i6) (Litex.denote (Litex.RPos (M := M))) := ((Litex.positiveReal_members (M := M) (Litex.denote _value_i6)).mpr ⟨_preimage_members, _preimage_positive_i2⟩)
                    exact _preimage_output)
                )
            )
          have h_144 : Litex.In _value_i6 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_161
                )
            )
          have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i6 h_144)
                )
            )
          have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_171)
                )
            )
          have h_173 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_171) _litex_zero.symm)
                )
            )
          have h_145 : (by
            let _equal_wd_1_0 := (by
              have _preimage_domain := ((Litex.preimageMembers (_object_w16 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i6)).mp (Litex.inOfSame _value_i6 _value_i6 (_object_w16 (M := M)) (_object_w16 (M := M)) (Litex.sameRefl _value_i6) (show @Eq M.Value _ _ from Eq.refl _) h_159)).1
              exact Litex.callOn (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (_object_i1 (M := M)) _value_i6 (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) _preimage_domain)
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  h_162
                )
            )
          exact (And.intro h_144 h_145)
        )
      )
  )

theorem h_175 : (by
  let _atomic_wd_1_0 := (_object_w16 (M := M))
  exact Litex.Subset _atomic_wd_1_0 (Litex.RPos (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w16 (M := M))
          exact (by
            let _preimage := _atomic_wd_1_0
            let _preimage_builder := (Litex.setBuilder (Litex.RPos (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i8 (Litex.RPos (M := M))) => Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) _value_i8 (h_75 (M := M)) (Litex.inRPos_real _value_i8 h_177) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i8)).mp h_177).2) (Litex.number (M := M) (3 : ℂ))))
            change Litex.Subset _preimage (Litex.RPos (M := M))
            intro _preimage_input _preimage_member
            have _preimage_domain := ((Litex.preimageMembers _preimage (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) _preimage_input).mp _preimage_member).1
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _litex_input) _).mp _preimage_domain
            have _preimage_positive_i2 := _preimage_guard
            have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.RPos (M := M))) := ((Litex.positiveReal_members (M := M) _preimage_input).mpr ⟨_preimage_members, _preimage_positive_i2⟩)
            exact Eq.mp (congrArg (M.mem _preimage_input) (Litex.sameRefl (Litex.RPos (M := M)))) _preimage_base))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_domain_x5f_preimages_x2f_statement_x2e_lit
