import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_rational_x5f_product_x5f_theorem_x2f_statement_x2e_lit

universe u v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.QStar (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.QStar (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.QStar (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.QStar (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _raw_i2) (Litex.denote (Litex.QStar (M := M))) := (by
    intro _raw_i2 h_14 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.QStar (M := M)) := h_14
    have h_15 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inQStar_nonzero _value_i2 h_14)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i2 (Litex.inQStar_base _value_i2 h_14)) h_15)
      exact Litex.In _atomic_wd_1_0 (Litex.QStar (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i2 (Litex.inQStar_base _value_i2 h_14)) h_15)
      exact (Litex.divInQStar _atomic_wd_1_0 (Litex.inQStar_intro (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInQOfEq (M := M) (1 : ℂ) (1 : ℚ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) 0) (1 : ℂ) 0 (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) rfl (by norm_num [Complex.ext_iff]))) h_14)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.QStar (M := M))) (Litex.denote (Litex.QStar (M := M))) (Litex.isSet (Litex.QStar (M := M))) (Litex.isSet (Litex.QStar (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_94 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_95 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_97 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_103 : Litex.In _value_i3 (Litex.QStar (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_105 : Litex.In _value_i4 (Litex.QStar (M := M))), (by
  let _equal_wd_1_0 := (let _object_w9 := (Litex.mul _value_i3 _value_i4 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_103)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_105)));
  (let _litex_call_arg_0 := _object_w9;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
    let _atomic_wd_1_0 := _object_w9
    exact (Litex.mulInQStar _atomic_wd_1_0 h_103 h_105)), True.intro⟩)))
  let _equal_wd_1_1 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i3;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_103, True.intro⟩));
  let _wd_1_1 := (let _litex_call_arg_0 := _value_i4;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_105, True.intro⟩));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_103 _Host_i4 _rep_i4 _value_i4 h_105
          have h_104 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i3 h_103)
                )
            )
          have h_106 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i4 h_105)
                )
            )
          have h_385 : Litex.In _value_i3 (Litex.QStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_103
                )
            )
          have h_387 : Litex.In _value_i4 (Litex.QStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_105
                )
            )
          have h_386 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i3 h_385)
                )
            )
          have h_388 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i4 h_387)
                )
            )
          let _object_w29 := (let _object_w12 := (Litex.mul _value_i3 _value_i4 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387)));
          (let _litex_call_arg_0 := _object_w12;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.mulInQStar _atomic_wd_1_0 h_385 h_387)), True.intro⟩)))

          let _object_w30 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.mul _value_i3 _value_i4 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387)));
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.mulInC _value_i3 _value_i4 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((Litex.NativeBridge.asComplex _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385))) * (Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387)))) (0 : ℂ) (Litex.NativeBridge.denoteMul _value_i3 _value_i4 (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (mul_ne_zero (Litex.NativeBridge.nativeNonzeroOfDenote _value_i3 (Litex.NativeBridge.asComplex _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385))) h_386) (Litex.NativeBridge.nativeNonzeroOfDenote _value_i4 (Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387))) h_388))))))

          have h_98 : (by
            let _equal_wd_1_0 := _object_w29
            let _equal_wd_1_1 := _object_w30
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w29;
                  let _equal_wd_1_1 := _object_w30;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i4))) = (M.divValue (M.number (1 : ℂ)) (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i4))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _object_w28 := (_equal_wd_1_1).val.right;
                  (let _litex_call_arg_0 := _object_w28;
                  Litex.callOnDomain (Litex.QStar (M := M)) (Litex.QStar (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
                    let _atomic_wd_1_0 := _object_w28
                    exact (Litex.mulInQStar _atomic_wd_1_0 h_385 h_387)) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i4))); exact rfl))
                  )).trans (((show @Eq M.Value _ _ from Eq.refl _)).trans ((Eq.refl (M.divValue (M.number (1 : ℂ)) (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i4))))).symm))))
                )
            )
          let _object_w31 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_385, True.intro⟩))

          let _object_w32 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385)) h_386)

          have h_99 : (by
            let _equal_wd_1_0 := _object_w31
            let _equal_wd_1_1 := _object_w32
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w31;
                  let _equal_wd_1_1 := _object_w32;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i3)) from by
                    have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i3)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i3)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i3)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i3;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.QStar (M := M)) (Litex.QStar (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_385 True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i3)); exact rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w33 := (let _litex_call_arg_0 := _value_i4;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_387, True.intro⟩))

          let _object_w34 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387)) h_388)

          have h_100 : (by
            let _equal_wd_1_0 := _object_w33
            let _equal_wd_1_1 := _object_w34
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w33;
                  let _equal_wd_1_1 := _object_w34;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) from by
                    have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i4;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.QStar (M := M)) (Litex.QStar (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_387 True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)); exact rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w35 := (let _wd_1_0 := _object_w31;
          let _wd_1_1 := _object_w33;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w31
            exact (Litex.rationalToComplex _object_w31 (Litex.inQStar_base _object_w31 (Litex.callOnInOutput _object_w31)))) (by
            let _atomic_wd_1_0 := _object_w33
            exact (Litex.rationalToComplex _object_w33 (Litex.inQStar_base _object_w33 (Litex.callOnInOutput _object_w33))))))

          let _object_w36 := (let _wd_1_0 := _object_w32;
          let _wd_1_1 := _object_w34;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w32
            exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385)) (_atomic_wd_1_0).wd.2.2)) (by
            let _atomic_wd_1_0 := _object_w34
            exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387)) (_atomic_wd_1_0).wd.2.2))))

          have h_101 : (by
            let _equal_wd_1_0 := _object_w35
            let _equal_wd_1_1 := _object_w36
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i3)) from h_99) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) from h_100))
                )
            )
          have h_102 : (by
            let _equal_wd_1_0 := _object_w36
            let _equal_wd_1_1 := _object_w30
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ (((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385)))) * ((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387))))) ((1 : ℂ) / ((Litex.NativeBridge.asComplex _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385))) * (Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387))))) (Litex.NativeBridge.denoteMul (_object_w36).val.left (_object_w36).val.right (_object_w36).wd.1 (_object_w36).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) _value_i3 (_object_w32).wd.1 (_object_w32).wd.2.1 (_object_w32).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) _value_i4 (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387))))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (_object_w30).val.right (_object_w30).wd.1 (_object_w30).wd.2.1 (_object_w30).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteMul _value_i3 _value_i4 ((_object_w30).val.right).wd.1 ((_object_w30).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387))))) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i3 (Litex.NativeBridge.asComplex _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_385))) h_386
                    have _litex_nz_1 : ((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i4 (Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_387))) h_388
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))
                )
            )
          exact ((((h_98).trans (h_102).symm)).trans (h_101).symm)
        )
      )
  )

theorem h_5529 : (by
  have h_5530 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.QStar (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inQStar_intro (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) 0) (2 : ℂ) 0 (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) rfl (by norm_num [Complex.ext_iff])))
        )
    )
  have h_5531 : (by
    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.QStar (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
            exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq (- (3 : ℂ)) (-3 : ℚ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) (- (3 : ℂ)) 0 (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) rfl (by norm_num [Complex.ext_iff]))))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _object_w44 := (let _wd_2_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_2_1 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ))))));
    (let _litex_call_arg_0 := _object_w44;
    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
      let _atomic_wd_1_0 := _object_w44
      exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) * (- (3 : ℂ))) (Litex.Q (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_object_w44).val.right (_object_w44).wd.1 (_object_w44).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) (Litex.NativeBridge.numberInQOfEq ((2 : ℂ) * (- (3 : ℂ))) (-6 : ℚ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) ((2 : ℂ) * (- (3 : ℂ))) 0 (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_object_w44).val.right (_object_w44).wd.1 (_object_w44).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) rfl (by norm_num [Complex.ext_iff])))), True.intro⟩)))
    let _equal_wd_1_1 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_5530, True.intro⟩));
    let _wd_1_1 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
    (let _litex_call_arg_0 := _wd_2_0;
    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
      let _atomic_wd_1_0 := _wd_2_0
      exact h_5531), True.intro⟩)));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))))))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_5530 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.QStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_intro (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) 0) (2 : ℂ) 0 (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) rfl (by norm_num [Complex.ext_iff])))
                )
            )
          have h_5535 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero (Litex.number (M := M) (2 : ℂ)) h_5530)
                )
            )
          have h_5531 : (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
            exact Litex.In _atomic_wd_1_0 (Litex.QStar (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                    exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq (- (3 : ℂ)) (-3 : ℚ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) (- (3 : ℂ)) 0 (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) rfl (by norm_num [Complex.ext_iff]))))
                )
            )
          have h_5545 : ¬ Litex.Same (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) h_5531)
                )
            )
          have h_5532 : Litex.Same (let _object_w44 := (let _wd_2_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_2_1 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ))))));
          (let _litex_call_arg_0 := _object_w44;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
            let _atomic_wd_1_0 := _object_w44
            exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) * (- (3 : ℂ))) (Litex.Q (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_object_w44).val.right (_object_w44).wd.1 (_object_w44).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) (Litex.NativeBridge.numberInQOfEq ((2 : ℂ) * (- (3 : ℂ))) (-6 : ℚ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) ((2 : ℂ) * (- (3 : ℂ))) 0 (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_object_w44).val.right (_object_w44).wd.1 (_object_w44).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) rfl (by norm_num [Complex.ext_iff])))), True.intro⟩))) (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_5530, True.intro⟩));
          let _wd_1_1 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
          (let _litex_call_arg_0 := _wd_2_0;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
            let _atomic_wd_1_0 := _wd_2_0
            exact h_5531), True.intro⟩)));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_97 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_5530 (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) h_5531)
                )
            )
          exact (let _equal_wd_1_0 := (let _object_w44 := (let _wd_2_0 := (Litex.number (M := M) (2 : ℂ));
        let _wd_2_1 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
        (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ))))));
        (let _litex_call_arg_0 := _object_w44;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
          let _atomic_wd_1_0 := _object_w44
          exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) * (- (3 : ℂ))) (Litex.Q (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_object_w44).val.right (_object_w44).wd.1 (_object_w44).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) (Litex.NativeBridge.numberInQOfEq ((2 : ℂ) * (- (3 : ℂ))) (-6 : ℚ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) ((2 : ℂ) * (- (3 : ℂ))) 0 (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_object_w44).val.right (_object_w44).wd.1 (_object_w44).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) rfl (by norm_num [Complex.ext_iff])))), True.intro⟩)));
        let _equal_wd_1_1 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_5530, True.intro⟩));
        let _wd_1_1 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
        (let _litex_call_arg_0 := _wd_2_0;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
          let _atomic_wd_1_0 := _wd_2_0
          exact h_5531), True.intro⟩)));
        (Litex.mul _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))))));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_5532).trans (Litex.sameRefl _equal_wd_1_1)))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_rational_x5f_product_x5f_theorem_x2f_statement_x2e_lit
