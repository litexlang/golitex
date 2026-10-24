import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_natural_x5f_successor_x5f_affine_x5f_identity_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
  have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalNonnegative _value_i2 h_14)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))))
theorem h_61 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_62 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_64 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_77 : Litex.In _value_i3 (Litex.N (M := M))), (by
  let _object_w9 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_61 (M := M)) h_77 True.intro);
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  let _object_w10 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_77));
  (Litex.add _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.mulInC _wd_1_0 _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_77)))))
  exact (by
    let _equal_wd_1_0 := _object_w9
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_77
          have h_78 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i3 h_77)
                )
            )
          let _object_w9 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_61 (M := M)) h_77 True.intro);
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
          let _object_w10 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_77));
          (Litex.add _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.mulInC _wd_1_0 _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_77)))))
          have h_63 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w9;
                  let _equal_wd_1_1 := _object_w10;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.mulValue (Eq.refl (M.number (2 : ℂ))) (by
                    let _litex_original := (_equal_wd_1_0).val.right
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i3;
                    (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_77 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_62 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) from rfl))
                  ))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
                  let _wd_1_1 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_77) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.addInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_77) (Litex.numberInC (M := M) (1 : ℂ))))));
                  let _equal_wd_2_1 := _equal_wd_1_1;
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((2 : ℂ) * ((Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_77)) + (1 : ℂ))) ((2 : ℂ) + ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_77)))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteAdd _value_i3 (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_0).val.right).wd.1 ((_equal_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.naturalToComplex _value_i3 h_77)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i3 ((_equal_wd_2_1).val.right).wd.1 ((_equal_wd_2_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.naturalToComplex _value_i3 h_77)))) (by ring!))))).trans ((Eq.refl (M.addValue (M.number (2 : ℂ)) (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i3))))).symm))))
                )
            )
          exact h_63
        )
      )
  )

noncomputable def _object_w11 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_61 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)

theorem h_1145 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.number (3 : ℂ)) from by
          have _litex_residual : (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = (M.number (3 : ℂ)) := (let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))))).trans (by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_62 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_natural_x5f_successor_x5f_affine_x5f_identity_x2f_statement_x2e_lit
