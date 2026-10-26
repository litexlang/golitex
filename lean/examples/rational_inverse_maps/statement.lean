import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit

universe u v1 v2 v3 v10 v12 v14 v16 v18 v19
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.Q (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))), (by
  let _object_w3 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i1 h_16) (Litex.numberInC (M := M) (1 : ℂ)))
  exact (by
    let _atomic_wd_1_0 := _object_w3
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
          let _object_w3 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i1 h_16) (Litex.numberInC (M := M) (1 : ℂ)))
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i1 h_16) (Litex.numberInC (M := M) (1 : ℂ)) h_1) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact h_2
        )
      )
  )

theorem h_58 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_72 : Litex.In _value_i2 (Litex.Q (M := M))) (h_56 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ))), (by
  let _object_w7 := (Litex.sub _value_i2 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i2 h_72) (Litex.numberInC (M := M) (2 : ℂ)))
  exact (by
    let _atomic_wd_1_0 := _object_w7
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_72 h_56
          let _object_w7 := (Litex.sub _value_i2 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i2 h_72) (Litex.numberInC (M := M) (2 : ℂ)))
          have h_57 : (by
            let _atomic_wd_1_0 := _object_w7
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i2 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i2 h_72) (Litex.numberInC (M := M) (2 : ℂ)) h_56) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact h_57
        )
      )
  )

theorem h_114 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_129 : Litex.In _value_i3 (Litex.Q (M := M))) (h_112 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w11 := (Litex.div (Litex.number (M := M) (3 : ℂ)) _value_i3 (Litex.numberInC (M := M) (3 : ℂ)) (Litex.rationalToComplex _value_i3 h_129) h_112)
  exact (by
    let _atomic_wd_1_0 := _object_w11
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_129 h_112
          let _object_w11 := (Litex.div (Litex.number (M := M) (3 : ℂ)) _value_i3 (Litex.numberInC (M := M) (3 : ℂ)) (Litex.rationalToComplex _value_i3 h_129) h_112)
          have h_113 : (by
            let _atomic_wd_1_0 := _object_w11
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (3 : ℂ)) _value_i3 (Litex.numberInC (M := M) (3 : ℂ)) (Litex.rationalToComplex _value_i3 h_129) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_112) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact h_113
        )
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) _raw_i5) (M.number (1 : ℂ))) (M.subValue _raw_i5 (M.number (1 : ℂ))))) (by
  intro _raw_i5 h_216 h_177
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_216)
  have h_216 : Litex.In _value_i5 (Litex.Q (M := M)) := h_216
  have h_177 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i5 = (M.number (1 : ℂ))))
            exact h_177)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i5 h_216));
    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i5 h_216))) (Litex.numberInC (M := M) (1 : ℂ))));
    let _wd_1_1 := (Litex.sub _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i5 h_216) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i5 h_216)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.subInC _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i5 h_216) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i5 h_216) (Litex.numberInC (M := M) (1 : ℂ)) h_177) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
    exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i5 h_216));
    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i5 h_216))) (Litex.numberInC (M := M) (1 : ℂ))));
    let _wd_1_1 := (Litex.sub _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i5 h_216) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i5 h_216)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.subInC _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i5 h_216) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i5 h_216) (Litex.numberInC (M := M) (1 : ℂ)) h_177) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
    exact (Litex.divInQ (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.addInQ ((_atomic_wd_1_0).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInQ (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num)) h_216) (Litex.NativeBridge.numberInQOfEq (M := M) (1 : ℂ) (1 : ℚ) (by norm_num))) (Litex.subInQ _value_i5 (Litex.number (M := M) (1 : ℂ)) h_216 (Litex.NativeBridge.numberInQOfEq (M := M) (1 : ℂ) (1 : ℚ) (by norm_num))) (_atomic_wd_1_0).wd.2.2))))
theorem h_627 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_628 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

noncomputable def _object_i7 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (by
  intro _raw_i8 h_668 h_629
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_668)
  have h_668 : Litex.In _value_i8 (Litex.Q (M := M)) := h_668
  have h_629 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (2 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i8 = (M.number (2 : ℂ))))
            exact h_629)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := (Litex.sub _value_i8 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.subInC _value_i8 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (2 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i8 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (2 : ℂ)) h_629) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
    exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := (Litex.sub _value_i8 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.subInC _value_i8 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (2 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i8 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i8 h_668) (Litex.numberInC (M := M) (2 : ℂ)) h_629) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
    exact (Litex.divInQ (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.addInQ _value_i8 (Litex.number (M := M) (1 : ℂ)) h_668 (Litex.NativeBridge.numberInQOfEq (M := M) (1 : ℂ) (1 : ℚ) (by norm_num))) (Litex.subInQ _value_i8 (Litex.number (M := M) (2 : ℂ)) h_668 (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num))) (_atomic_wd_1_0).wd.2.2))))
theorem h_1038 : Litex.In (_object_i7 (M := M)) (Litex.fnSet ((_object_i7 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i7 (M := M)))
      )
  )
theorem h_1039 : Litex.Same (_object_i7 (M := M)) (_object_i7 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i7 (M := M)))
      )
  )

theorem h_1042 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_1046 : Litex.In _value_i10 (Litex.Q (M := M))) (h_1040 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (1 : ℂ))), (by
  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i10 (h_627 (M := M)) h_1046 h_1040)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_1046 h_1040
          have h_1058 : Litex.In _value_i10 (Litex.Q (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1046
                )
            )
          let _object_w30 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i10 (h_627 (M := M)) h_1058 h_1040)

          let _object_w31 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i10 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058));
          let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i10 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058))) (Litex.numberInC (M := M) (1 : ℂ))));
          let _wd_1_1 := (Litex.sub _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i10 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058) (Litex.numberInC (M := M) (1 : ℂ)) h_1040) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

          have h_1043 : (by
            let _equal_wd_1_0 := _object_w30
            let _equal_wd_1_1 := _object_w31
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w30;
                  let _equal_wd_1_1 := _object_w31;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i10)) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i10)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from by
                    have _litex_residual : (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i10)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i10)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i10)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i10)) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i10)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                    let _wd_1_1 := _value_i10;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1058 h_1040))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_628 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) _raw_i5) (M.number (1 : ℂ))) (M.subValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) _raw_i5) (M.number (1 : ℂ))) (M.subValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i10)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w32 := (let _wd_1_0 := _object_w30;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w30
            exact (Litex.rationalToComplex _object_w30 (Litex.callInOutput _object_w30))) (Litex.numberInC (M := M) (2 : ℂ))))

          let _object_w33 := (let _wd_1_0 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_1 := (_object_w31).val.right;
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058) (Litex.numberInC (M := M) (1 : ℂ)) h_1040) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

          have h_1044 : (by
            let _equal_wd_1_0 := _object_w32
            let _equal_wd_1_1 := _object_w33
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w32;
                  let _equal_wd_1_1 := _object_w33;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i10)) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i10)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from by
                    let _litex_original := _object_w30
                    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                    let _wd_1_1 := _value_i10;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1058 h_1040))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_628 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) _raw_i5) (M.number (1 : ℂ))) (M.subValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) _raw_i5) (M.number (1 : ℂ))) (M.subValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i10)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i10) (M.number (1 : ℂ)))) from rfl))
                  ) (Eq.refl (M.number (2 : ℂ))))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := _object_w31;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.sub _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w31
                    exact (Litex.divInC (_object_w31).val.left (_equal_wd_1_1).val.right (Litex.addInC ((_object_w31).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC _wd_1_1 _value_i10 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (2 : ℂ))));
                  let _equal_wd_2_1 := _equal_wd_1_1;
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_1058))) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_1058)) - (1 : ℂ))) - (2 : ℂ)) ((3 : ℂ) / ((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_1058)) - (1 : ℂ))) (Litex.NativeBridge.denoteSub (_equal_wd_2_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w31).val.left (_object_w31).val.right (_object_w31).wd.1 (_object_w31).wd.2.1 (_object_w31).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_object_w31).val.left).val.left (Litex.number (M := M) (1 : ℂ)) ((_object_w31).val.left).wd.1 ((_object_w31).val.left).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i10 (((_object_w31).val.left).val.left).wd.1 (((_object_w31).val.left).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_1058))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i10 (Litex.number (M := M) (1 : ℂ)) ((_object_w31).val.right).wd.1 ((_object_w31).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_1058)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteSub _value_i10 (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_1).val.right).wd.1 ((_equal_wd_2_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_1058)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by
                    have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_1058)) - (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_equal_wd_2_1).val.right ((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_1058)) - (1 : ℂ)) (Litex.NativeBridge.denoteSub _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_1058)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
                    let _atomic_wd_1_0 := (_equal_wd_2_1).val.right
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058) (Litex.numberInC (M := M) (1 : ℂ)) h_1040) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))).trans ((Eq.refl (M.divValue (M.number (3 : ℂ)) (M.subValue (Litex.denote _value_i10) (M.number (1 : ℂ)))))).symm))))
                )
            )
          have h_1045 : (by
            let _atomic_wd_1_0 := _object_w33
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w33
                    exact (by
                      have h_5858 : (by
                        let _atomic_wd_2_0 := (_object_w33).val.right
                        exact Litex.In _atomic_wd_2_0 (Litex.Q (M := M))) :=
                        (by
                          let _atomic_wd_2_0 := (_object_w33).val.right
                          exact (Litex.subInQ _value_i10 (Litex.number (M := M) (1 : ℂ)) h_1058 (Litex.NativeBridge.numberInQOfEq (M := M) (1 : ℂ) (1 : ℚ) (by norm_num))))
                      have h_5905 : (by
                        let _atomic_wd_2_0 := (_object_w33).val.right
                        exact ¬ Litex.Same _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ))) :=
                        (by
                          let _atomic_wd_2_0 := (_object_w33).val.right
                          exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i10 h_1058) (Litex.numberInC (M := M) (1 : ℂ)) h_1040) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (congrArg₂ M.divValue (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (Litex.sameRefl (_object_w33).val.right)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_114 (M := M)) (_object_w33).val.right h_5858 h_5905))
                    ))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w30
            exact (Litex.notSameOfSubNonzero _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (let _litex_numeric_call := _object_w30;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.Q from (Litex.callInOutput _litex_numeric_call)));
            _litex_numeric_member) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _object_w33 _object_w32 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_1044).symm (show @Eq M.Value _ _ from Eq.refl _) h_1045)))
        )
      )
  )

theorem h_5990 : ∀ {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_5994 : Litex.In _value_i12 (Litex.Q (M := M))) (h_5988 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (2 : ℂ))), (by
  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _value_i12 (h_1038 (M := M)) h_5994 h_5988)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i12 _rep_i12 _value_i12 h_5994 h_5988
          have h_6006 : Litex.In _value_i12 (Litex.Q (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5994
                )
            )
          let _object_w41 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _value_i12 (h_1038 (M := M)) h_6006 h_5988)

          let _object_w42 := (let _wd_1_0 := (Litex.add _value_i12 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.sub _value_i12 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i12 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i12 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (2 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i12 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (2 : ℂ)) h_5988) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

          have h_5991 : (by
            let _equal_wd_1_0 := _object_w41
            let _equal_wd_1_1 := _object_w42
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w41;
                  let _equal_wd_1_1 := _object_w42;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i12)) = (M.divValue (M.addValue (Litex.denote _value_i12) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i12) (M.number (2 : ℂ)))) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i12) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i12) (M.number (2 : ℂ)))) = (M.divValue (M.addValue (Litex.denote _value_i12) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i12) (M.number (2 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i12)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i12)) = (M.divValue (M.addValue (Litex.denote _value_i12) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i12) (M.number (2 : ℂ)))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                    let _wd_1_1 := _value_i12;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_6006 h_5988))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1039 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i12) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i12) (M.number (2 : ℂ)))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w43 := (let _wd_1_0 := _object_w41;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w41
            exact (Litex.rationalToComplex _object_w41 (Litex.callInOutput _object_w41))) (Litex.numberInC (M := M) (1 : ℂ))))

          let _object_w44 := (let _wd_1_0 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_1 := (_object_w42).val.right;
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i12 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (2 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i12 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (2 : ℂ)) h_5988) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

          have h_5992 : (by
            let _equal_wd_1_0 := _object_w43
            let _equal_wd_1_1 := _object_w44
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w43;
                  let _equal_wd_1_1 := _object_w44;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i12)) = (M.divValue (M.addValue (Litex.denote _value_i12) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i12) (M.number (2 : ℂ)))) from by
                    let _litex_original := _object_w41
                    let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                    let _wd_1_1 := _value_i12;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_6006 h_5988))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1039 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i12) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i12) (M.number (2 : ℂ)))) from rfl))
                  ) (Eq.refl (M.number (1 : ℂ))))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := _object_w42;
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.sub _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w42
                    exact (Litex.divInC (_object_w42).val.left (_equal_wd_1_1).val.right (Litex.addInC _value_i12 _wd_1_1 (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i12 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (2 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))));
                  let _equal_wd_2_1 := _equal_wd_1_1;
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((((Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_6006)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_6006)) - (2 : ℂ))) - (1 : ℂ)) ((3 : ℂ) / ((Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_6006)) - (2 : ℂ))) (Litex.NativeBridge.denoteSub (_equal_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w42).val.left (_object_w42).val.right (_object_w42).wd.1 (_object_w42).wd.2.1 (_object_w42).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i12 (Litex.number (M := M) (1 : ℂ)) ((_object_w42).val.left).wd.1 ((_object_w42).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_6006)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i12 (Litex.number (M := M) (2 : ℂ)) ((_object_w42).val.right).wd.1 ((_object_w42).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_6006)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteSub _value_i12 (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_1).val.right).wd.1 ((_equal_wd_2_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_6006)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (by
                    have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_6006)) - (2 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_equal_wd_2_1).val.right ((Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_6006)) - (2 : ℂ)) (Litex.NativeBridge.denoteSub _value_i12 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_6006)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by
                    let _atomic_wd_1_0 := (_equal_wd_2_1).val.right
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i12 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (2 : ℂ)) h_5988) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))).trans ((Eq.refl (M.divValue (M.number (3 : ℂ)) (M.subValue (Litex.denote _value_i12) (M.number (2 : ℂ)))))).symm))))
                )
            )
          have h_5993 : (by
            let _atomic_wd_1_0 := _object_w44
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w44
                    exact (by
                      have h_10186 : (by
                        let _atomic_wd_2_0 := (_object_w44).val.right
                        exact Litex.In _atomic_wd_2_0 (Litex.Q (M := M))) :=
                        (by
                          let _atomic_wd_2_0 := (_object_w44).val.right
                          exact (Litex.subInQ _value_i12 (Litex.number (M := M) (2 : ℂ)) h_6006 (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num))))
                      have h_10233 : (by
                        let _atomic_wd_2_0 := (_object_w44).val.right
                        exact ¬ Litex.Same _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ))) :=
                        (by
                          let _atomic_wd_2_0 := (_object_w44).val.right
                          exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i12 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i12 h_6006) (Litex.numberInC (M := M) (2 : ℂ)) h_5988) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (congrArg₂ M.divValue (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (Litex.sameRefl (_object_w44).val.right)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_114 (M := M)) (_object_w44).val.right h_10186 h_10233))
                    ))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w41
            exact (Litex.notSameOfSubNonzero _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (let _litex_numeric_call := _object_w41;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.Q from (Litex.callInOutput _litex_numeric_call)));
            _litex_numeric_member) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.notSameOfSame _object_w44 _object_w43 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_5992).symm (show @Eq M.Value _ _ from Eq.refl _) h_5993)))
        )
      )
  )

theorem h_10318 : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_10324 : Litex.In _value_i14 (Litex.Q (M := M))) (h_10316 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (1 : ℂ))), (by
  let _equal_wd_1_0 := (let _object_w50 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i14 (h_627 (M := M)) h_10324 h_10316);
  (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _object_w50 (h_1038 (M := M)) (by
    let _atomic_wd_1_0 := _object_w50
    exact (by
      let _litex_return_call := _object_w50
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
    let _atomic_wd_1_0 := _object_w50
    exact (by
      have h_10415 : Litex.In _value_i14 (Litex.Q (M := M)) :=
        h_10324
      have h_10420 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (1 : ℂ)) :=
        h_10316
      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i14)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i14 h_10415 h_10420))
    ))))
  exact Litex.Same _equal_wd_1_0 _value_i14) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_10324 h_10316
          have h_10425 : Litex.In _value_i14 (Litex.Q (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10324
                )
            )
          let _object_w53 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i14 (h_627 (M := M)) h_10425 h_10316)

          have h_10319 : (by
            let _atomic_wd_1_0 := _object_w53
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w53
                    exact (by
                      have h_10460 : Litex.In _value_i14 (Litex.Q (M := M)) :=
                        h_10425
                      have h_10465 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (1 : ℂ)) :=
                        h_10316
                      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i14)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i14 h_10460 h_10465))
                    ))
                )
            )
          let _object_w55 := (let _wd_1_0 := _object_w53;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w53
            exact (Litex.rationalToComplex _object_w53 (Litex.callInOutput _object_w53))) (Litex.numberInC (M := M) (2 : ℂ))))

          have h_10320 : (by
            let _atomic_wd_1_0 := _object_w55
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w55
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (let _litex_numeric_call := _object_w53;
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.Q from (Litex.callInOutput _litex_numeric_call)));
                    _litex_numeric_member) (Litex.numberInC (M := M) (2 : ℂ)) (by
                      let _atomic_wd_2_0 := _object_w53
                      exact h_10319)) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          let _object_w57 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425));
          let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425))) (Litex.numberInC (M := M) (1 : ℂ))));
          let _wd_1_1 := (Litex.sub _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ)) h_10316) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

          have h_10321 : (by
            let _equal_wd_1_0 := _object_w53
            let _equal_wd_1_1 := _object_w57
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i14) (M.number (1 : ℂ)))) from by
                    have _litex_residual : (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i14) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i14) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i14) (M.number (1 : ℂ)))) from by
                    let _litex_original := _object_w53
                    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                    let _wd_1_1 := _value_i14;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_10425 h_10316))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_628 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) _raw_i5) (M.number (1 : ℂ))) (M.subValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) _raw_i5) (M.number (1 : ℂ))) (M.subValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i14) (M.number (1 : ℂ)))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w58 := (let _wd_1_0 := _object_w57;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w57
            exact (Litex.divInC (_object_w57).val.left (_object_w57).val.right (Litex.addInC ((_object_w57).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC _wd_1_1 _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (2 : ℂ))))

          have h_10322 : (by
            let _atomic_wd_1_0 := _object_w58
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w58
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (Litex.divInC (_object_w57).val.left (_object_w57).val.right (_object_w57).wd.1 (_object_w57).wd.2.1 (_object_w57).wd.2.2) (Litex.numberInC (M := M) (2 : ℂ)) (by
                      let _atomic_wd_2_0 := _object_w57
                      exact (Litex.notSameOfSame (_object_w55).val.left _atomic_wd_2_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_10321 (show @Eq M.Value _ _ from Eq.refl _) h_10319))) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          have h_10323 : (by
            let _chain_wd_10323_0 := (let _wd_1_0 := _object_w53;
            (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
              let _atomic_wd_1_0 := _object_w53
              exact (by
                let _litex_return_call := _object_w53
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
              let _atomic_wd_1_0 := _object_w53
              exact h_10319)))
            let _chain_wd_10323_1 := (let _wd_1_0 := (let _wd_2_0 := _object_w53;
            let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w53
              exact (Litex.rationalToComplex _object_w53 (Litex.callInOutput _object_w53))) (Litex.numberInC (M := M) (1 : ℂ))));
            let _wd_1_1 := _object_w55;
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _arithmetic := _atomic_wd_1_0
                exact Litex.addInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
              let _atomic_wd_1_0 := _object_w55
              exact (by
                let _arithmetic := _atomic_wd_1_0
                exact Litex.subInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
              let _atomic_wd_1_0 := _object_w55
              exact h_10320)))
            let _chain_wd_10323_2 := _chain_wd_10323_1
            let _chain_wd_10323_3 := (let _wd_1_0 := (let _wd_2_0 := _object_w57;
            let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w57
              exact (Litex.divInC (_object_w57).val.left (_object_w57).val.right (Litex.addInC ((_object_w57).val.left).val.left _wd_2_1 (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i14 _wd_2_1 (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))));
            let _wd_1_1 := _object_w58;
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w57).val.left (_object_w57).val.right (Litex.addInC ((_object_w57).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ))) ((_atomic_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (by
              let _atomic_wd_1_0 := _object_w58
              exact (Litex.subInC (_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (Litex.divInC (_object_w57).val.left (_object_w57).val.right (Litex.addInC ((_object_w57).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ))) ((_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (2 : ℂ)))) (by
              let _atomic_wd_1_0 := _object_w58
              exact h_10322)))
            let _chain_wd_10323_4 := _chain_wd_10323_3
            exact ((by
              let _equal_wd_1_0 := _chain_wd_10323_0
              let _equal_wd_1_1 := _chain_wd_10323_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_10323_2
              let _equal_wd_1_1 := _chain_wd_10323_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_10323_4
              exact Litex.Same _equal_wd_1_0 _value_i14)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_10323_0 := (let _wd_1_0 := _object_w53;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w53
                      exact (by
                        let _litex_return_call := _object_w53
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _object_w53
                      exact h_10319)))
                    let _chain_wd_10323_1 := (let _wd_1_0 := (let _wd_2_0 := _object_w53;
                    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.add _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _object_w53
                      exact (Litex.rationalToComplex _object_w53 (Litex.callInOutput _object_w53))) (Litex.numberInC (M := M) (1 : ℂ))));
                    let _wd_1_1 := _object_w55;
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.addInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
                      let _atomic_wd_1_0 := _object_w55
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.subInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
                      let _atomic_wd_1_0 := _object_w55
                      exact h_10320)))
                    let _chain_wd_10323_2 := _chain_wd_10323_1
                    let _chain_wd_10323_3 := (let _wd_1_0 := (let _wd_2_0 := _object_w57;
                    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.add _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _object_w57
                      exact (Litex.divInC (_object_w57).val.left (_object_w57).val.right (Litex.addInC ((_object_w57).val.left).val.left _wd_2_1 (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i14 _wd_2_1 (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))));
                    let _wd_1_1 := _object_w58;
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w57).val.left (_object_w57).val.right (Litex.addInC ((_object_w57).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ))) ((_atomic_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                      let _atomic_wd_1_0 := _object_w58
                      exact (Litex.subInC (_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (Litex.divInC (_object_w57).val.left (_object_w57).val.right (Litex.addInC ((_object_w57).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i14 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ))) ((_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (2 : ℂ)))) (by
                      let _atomic_wd_1_0 := _object_w58
                      exact h_10322)))
                    let _chain_wd_10323_4 := _chain_wd_10323_3
                    exact (And.intro (let _equal_wd_1_0 := _chain_wd_10323_0;
                    let _equal_wd_1_1 := _chain_wd_10323_1;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (2 : ℂ)))) from by
                      have _litex_residual : (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (2 : ℂ)))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (2 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (2 : ℂ)))) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                      let _wd_1_1 := _object_w53;
                      (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
                        let _atomic_wd_1_0 := _object_w53
                        exact (by
                          let _litex_return_call := _object_w53
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                        let _atomic_wd_1_0 := _object_w53
                        exact h_10319)))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1039 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (2 : ℂ)))) from rfl))
                    ))).trans _litex_residual))) (And.intro (congrArg₂ M.divValue (show (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (1 : ℂ))) = (M.addValue (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i14) (M.number (1 : ℂ)))) (M.number (1 : ℂ))) from (congrArg₂ M.addValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i14) (M.number (1 : ℂ)))) from h_10321) (show (M.number (1 : ℂ)) = (M.number (1 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) (M.number (2 : ℂ))) = (M.subValue (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i14) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) from (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i14)) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i14)) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i14) (M.number (1 : ℂ)))) from h_10321) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))))) (let _equal_wd_1_0 := _chain_wd_10323_4;
                    (show Litex.Same _equal_wd_1_0 _value_i14 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((((((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425))) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) - (1 : ℂ))) + (1 : ℂ)) / (((((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425))) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) - (1 : ℂ))) - (2 : ℂ))) (Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_equal_wd_1_0).val.left).val.left (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w57).val.left (_object_w57).val.right (_object_w57).wd.1 (_object_w57).wd.2.1 (_object_w57).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_object_w57).val.left).val.left (Litex.number (M := M) (1 : ℂ)) ((_object_w57).val.left).wd.1 ((_object_w57).val.left).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i14 (((_object_w57).val.left).val.left).wd.1 (((_object_w57).val.left).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.rationalToComplex _value_i14 h_10425))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i14 (Litex.number (M := M) (1 : ℂ)) ((_object_w57).val.right).wd.1 ((_object_w57).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub (_object_w58).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w58).wd.1 (_object_w58).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w57).val.left (_object_w57).val.right (_object_w57).wd.1 (_object_w57).wd.2.1 (_object_w57).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_object_w57).val.left).val.left (Litex.number (M := M) (1 : ℂ)) ((_object_w57).val.left).wd.1 ((_object_w57).val.left).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i14 (((_object_w57).val.left).val.left).wd.1 (((_object_w57).val.left).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.rationalToComplex _value_i14 h_10425))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i14 (Litex.number (M := M) (1 : ℂ)) ((_object_w57).val.right).wd.1 ((_object_w57).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) (by
                      have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) - (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_object_w57).val.right ((Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) - (1 : ℂ)) (Litex.NativeBridge.denoteSub _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
                      let _atomic_wd_1_0 := (_object_w57).val.right
                      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i14 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i14 h_10425) (Litex.numberInC (M := M) (1 : ℂ)) h_10316) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                      have _litex_nz_1 : ((((((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425))) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) - (1 : ℂ))) - (2 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_equal_wd_1_0).val.right (((((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425))) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) - (1 : ℂ))) - (2 : ℂ)) (Litex.NativeBridge.denoteSub (_object_w58).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w58).wd.1 (_object_w58).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w57).val.left (_object_w57).val.right (_object_w57).wd.1 (_object_w57).wd.2.1 (_object_w57).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_object_w57).val.left).val.left (Litex.number (M := M) (1 : ℂ)) ((_object_w57).val.left).wd.1 ((_object_w57).val.left).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i14 (((_object_w57).val.left).val.left).wd.1 (((_object_w57).val.left).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.rationalToComplex _value_i14 h_10425))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i14 (Litex.number (M := M) (1 : ℂ)) ((_object_w57).val.right).wd.1 ((_object_w57).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.rationalToComplex _value_i14 h_10425)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by
                      let _atomic_wd_1_0 := _object_w58
                      exact h_10322)
                      litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                    )))))))
                )
            )

          have h_20895 :=
            (And.left h_10323)

          have h_20896 :=
            (And.left (And.right h_10323))

          have h_20897 :=
            (And.right (And.right h_10323))

          have h_20898 :=
            h_20895

          have h_20899 :=
            h_20896

          have h_20900 :=
            h_20897

          have h_20901 :=
            (Eq.trans h_20895 h_20896)

          have h_20902 :=
            (Eq.trans (Eq.trans h_20895 h_20896) h_20897)

          have h_20903 :=
            (Eq.trans h_20896 h_20897)
          exact h_20902
        )
      )
  )

theorem h_21008 : ∀ {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_21014 : Litex.In _value_i16 (Litex.Q (M := M))) (h_21006 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (2 : ℂ))), (by
  let _equal_wd_1_0 := (let _object_w67 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _value_i16 (h_1038 (M := M)) h_21014 h_21006);
  (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _object_w67 (h_627 (M := M)) (by
    let _atomic_wd_1_0 := _object_w67
    exact (by
      let _litex_return_call := _object_w67
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
    let _atomic_wd_1_0 := _object_w67
    exact (by
      have h_21108 : Litex.In _value_i16 (Litex.Q (M := M)) :=
        h_21014
      have h_21113 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (2 : ℂ)) :=
        h_21006
      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i7 (M := M))) (Litex.sameRefl _value_i16)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((h_5990 (M := M)) _value_i16 h_21108 h_21113))
    ))))
  exact Litex.Same _equal_wd_1_0 _value_i16) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i16 _rep_i16 _value_i16 h_21014 h_21006
          have h_21118 : Litex.In _value_i16 (Litex.Q (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_21014
                )
            )
          let _object_w70 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _value_i16 (h_1038 (M := M)) h_21118 h_21006)

          have h_21009 : (by
            let _atomic_wd_1_0 := _object_w70
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w70
                    exact (by
                      have h_21156 : Litex.In _value_i16 (Litex.Q (M := M)) :=
                        h_21118
                      have h_21161 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (2 : ℂ)) :=
                        h_21006
                      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i7 (M := M))) (Litex.sameRefl _value_i16)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((h_5990 (M := M)) _value_i16 h_21156 h_21161))
                    ))
                )
            )
          let _object_w72 := (let _wd_1_0 := _object_w70;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w70
            exact (Litex.rationalToComplex _object_w70 (Litex.callInOutput _object_w70))) (Litex.numberInC (M := M) (1 : ℂ))))

          have h_21010 : (by
            let _atomic_wd_1_0 := _object_w72
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w72
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (let _litex_numeric_call := _object_w70;
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.Q from (Litex.callInOutput _litex_numeric_call)));
                    _litex_numeric_member) (Litex.numberInC (M := M) (1 : ℂ)) (by
                      let _atomic_wd_2_0 := _object_w70
                      exact h_21009)) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          let _object_w74 := (let _wd_1_0 := (Litex.add _value_i16 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.sub _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i16 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ)) h_21006) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

          have h_21011 : (by
            let _equal_wd_1_0 := _object_w70
            let _equal_wd_1_1 := _object_w74
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)) = (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) = (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)) = (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) from by
                    let _litex_original := _object_w70
                    let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                    let _wd_1_1 := _value_i16;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_21118 h_21006))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1039 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w75 := (let _wd_1_0 := _object_w74;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w74
            exact (Litex.divInC (_object_w74).val.left (_object_w74).val.right (Litex.addInC _value_i16 _wd_1_1 (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))))

          have h_21012 : (by
            let _atomic_wd_1_0 := _object_w75
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w75
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w74).val.left (_object_w74).val.right (_object_w74).wd.1 (_object_w74).wd.2.1 (_object_w74).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)) (by
                      let _atomic_wd_2_0 := _object_w74
                      exact (Litex.notSameOfSame (_object_w72).val.left _atomic_wd_2_0 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) h_21011 (show @Eq M.Value _ _ from Eq.refl _) h_21009))) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          have h_21013 : (by
            let _chain_wd_21013_0 := (let _wd_1_0 := _object_w70;
            (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _wd_1_0 (h_627 (M := M)) (by
              let _atomic_wd_1_0 := _object_w70
              exact (by
                let _litex_return_call := _object_w70
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
              let _atomic_wd_1_0 := _object_w70
              exact h_21009)))
            let _chain_wd_21013_1 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
            let _wd_3_1 := _object_w70;
            (Litex.mul _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
              let _atomic_wd_1_0 := _object_w70
              exact (Litex.rationalToComplex _object_w70 (Litex.callInOutput _object_w70)))));
            let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _wd_2_0
              exact (by
                let _arithmetic := _atomic_wd_1_0
                exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (Litex.numberInC (M := M) (1 : ℂ))));
            let _wd_1_1 := _object_w72;
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _arithmetic := _atomic_wd_1_0
                exact Litex.addInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
              let _atomic_wd_1_0 := _object_w72
              exact (by
                let _arithmetic := _atomic_wd_1_0
                exact Litex.subInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
              let _atomic_wd_1_0 := _object_w72
              exact h_21010)))
            let _chain_wd_21013_2 := _chain_wd_21013_1
            let _chain_wd_21013_3 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
            let _wd_3_1 := _object_w74;
            (Litex.mul _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
              let _atomic_wd_1_0 := _object_w74
              exact (Litex.divInC (_object_w74).val.left (_object_w74).val.right (Litex.addInC _value_i16 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i16 _wd_3_0 (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ))) (_atomic_wd_1_0).wd.2.2))));
            let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _wd_2_0
              exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (2 : ℂ)) (Litex.divInC (_object_w74).val.left (_object_w74).val.right (Litex.addInC _value_i16 _wd_2_1 (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ))) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (1 : ℂ))));
            let _wd_1_1 := _object_w75;
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.left).val.right (Litex.numberInC (M := M) (2 : ℂ)) (Litex.divInC (_object_w74).val.left (_object_w74).val.right (Litex.addInC _value_i16 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ))) (((_atomic_wd_1_0).val.left).val.right).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
              let _atomic_wd_1_0 := _object_w75
              exact (Litex.subInC ((_wd_1_0).val.left).val.right (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w74).val.left (_object_w74).val.right (Litex.addInC _value_i16 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ))) (((_wd_1_0).val.left).val.right).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (by
              let _atomic_wd_1_0 := _object_w75
              exact h_21012)))
            let _chain_wd_21013_4 := _chain_wd_21013_3
            exact ((by
              let _equal_wd_1_0 := _chain_wd_21013_0
              let _equal_wd_1_1 := _chain_wd_21013_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_21013_2
              let _equal_wd_1_1 := _chain_wd_21013_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_21013_4
              exact Litex.Same _equal_wd_1_0 _value_i16)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_21013_0 := (let _wd_1_0 := _object_w70;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _wd_1_0 (h_627 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w70
                      exact (by
                        let _litex_return_call := _object_w70
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _object_w70
                      exact h_21009)))
                    let _chain_wd_21013_1 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
                    let _wd_3_1 := _object_w70;
                    (Litex.mul _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
                      let _atomic_wd_1_0 := _object_w70
                      exact (Litex.rationalToComplex _object_w70 (Litex.callInOutput _object_w70)))));
                    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.add _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (Litex.numberInC (M := M) (1 : ℂ))));
                    let _wd_1_1 := _object_w72;
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.addInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
                      let _atomic_wd_1_0 := _object_w72
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.subInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
                      let _atomic_wd_1_0 := _object_w72
                      exact h_21010)))
                    let _chain_wd_21013_2 := _chain_wd_21013_1
                    let _chain_wd_21013_3 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
                    let _wd_3_1 := _object_w74;
                    (Litex.mul _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
                      let _atomic_wd_1_0 := _object_w74
                      exact (Litex.divInC (_object_w74).val.left (_object_w74).val.right (Litex.addInC _value_i16 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i16 _wd_3_0 (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ))) (_atomic_wd_1_0).wd.2.2))));
                    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.add _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (2 : ℂ)) (Litex.divInC (_object_w74).val.left (_object_w74).val.right (Litex.addInC _value_i16 _wd_2_1 (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ))) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (1 : ℂ))));
                    let _wd_1_1 := _object_w75;
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.left).val.right (Litex.numberInC (M := M) (2 : ℂ)) (Litex.divInC (_object_w74).val.left (_object_w74).val.right (Litex.addInC _value_i16 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ))) (((_atomic_wd_1_0).val.left).val.right).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                      let _atomic_wd_1_0 := _object_w75
                      exact (Litex.subInC ((_wd_1_0).val.left).val.right (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w74).val.left (_object_w74).val.right (Litex.addInC _value_i16 (Litex.number (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ))) (((_wd_1_0).val.left).val.right).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                      let _atomic_wd_1_0 := _object_w75
                      exact h_21012)))
                    let _chain_wd_21013_4 := _chain_wd_21013_3
                    exact (And.intro (let _equal_wd_1_0 := _chain_wd_21013_0;
                    let _equal_wd_1_1 := _chain_wd_21013_1;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16))) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16))) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)) (M.number (1 : ℂ)))) from by
                      have _litex_residual : (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16))) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16))) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16))) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16))) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)) (M.number (1 : ℂ)))) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                      let _wd_1_1 := _object_w70;
                      (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
                        let _atomic_wd_1_0 := _object_w70
                        exact (by
                          let _litex_return_call := _object_w70
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                        let _atomic_wd_1_0 := _object_w70
                        exact h_21009)))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_628 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) _raw_i5) (M.number (1 : ℂ))) (M.subValue _raw_i5 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) _raw_i5) (M.number (1 : ℂ))) (M.subValue _raw_i5 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16))) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)) (M.number (1 : ℂ)))) from rfl))
                    ))).trans _litex_residual))) (And.intro (((congrArg₂ M.divValue (congrArg₂ M.addValue (congrArg₂ M.mulValue (Eq.refl (M.number (2 : ℂ))) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)) = (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) from by
                      let _litex_original := _object_w70
                      let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                      let _wd_1_1 := _value_i16;
                      (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_21118 h_21006))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1039 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) from rfl))
                    )) (Eq.refl (M.number (1 : ℂ)))) (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i16)) = (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) from by
                      let _litex_original := _object_w70
                      let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                      let _wd_1_1 := _value_i16;
                      (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_21118 h_21006))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1039 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) from rfl))
                    ) (Eq.refl (M.number (1 : ℂ)))))).trans (((show @Eq M.Value _ _ from Eq.refl _)).trans ((Eq.refl (M.divValue (M.addValue (M.mulValue (M.number (2 : ℂ)) (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ))))) (M.number (1 : ℂ))) (M.subValue (M.divValue (M.addValue (Litex.denote _value_i16) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i16) (M.number (2 : ℂ)))) (M.number (1 : ℂ)))))).symm)) (let _equal_wd_1_0 := _chain_wd_21013_4;
                    (show Litex.Same _equal_wd_1_0 _value_i16 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((((2 : ℂ) * (((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) - (2 : ℂ)))) + (1 : ℂ)) / ((((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) - (2 : ℂ))) - (1 : ℂ))) (Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_equal_wd_1_0).val.left).val.left (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (((_equal_wd_1_0).val.left).val.left).val.right (((_equal_wd_1_0).val.left).val.left).wd.1 (((_equal_wd_1_0).val.left).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (_object_w74).val.left (_object_w74).val.right (_object_w74).wd.1 (_object_w74).wd.2.1 (_object_w74).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i16 (Litex.number (M := M) (1 : ℂ)) ((_object_w74).val.left).wd.1 ((_object_w74).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i16 (Litex.number (M := M) (2 : ℂ)) ((_object_w74).val.right).wd.1 ((_object_w74).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub (_object_w75).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w75).wd.1 (_object_w75).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w74).val.left (_object_w74).val.right (_object_w74).wd.1 (_object_w74).wd.2.1 (_object_w74).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i16 (Litex.number (M := M) (1 : ℂ)) ((_object_w74).val.left).wd.1 ((_object_w74).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i16 (Litex.number (M := M) (2 : ℂ)) ((_object_w74).val.right).wd.1 ((_object_w74).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) (by
                      have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) - (2 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_object_w74).val.right ((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) - (2 : ℂ)) (Litex.NativeBridge.denoteSub _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by
                      let _atomic_wd_1_0 := (_object_w74).val.right
                      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i16 (Litex.number (M := M) (2 : ℂ)) (Litex.rationalToComplex _value_i16 h_21118) (Litex.numberInC (M := M) (2 : ℂ)) h_21006) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                      have _litex_nz_1 : (((((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) - (2 : ℂ))) - (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_equal_wd_1_0).val.right ((((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) - (2 : ℂ))) - (1 : ℂ)) (Litex.NativeBridge.denoteSub (_object_w75).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w75).wd.1 (_object_w75).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w74).val.left (_object_w74).val.right (_object_w74).wd.1 (_object_w74).wd.2.1 (_object_w74).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i16 (Litex.number (M := M) (1 : ℂ)) ((_object_w74).val.left).wd.1 ((_object_w74).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i16 (Litex.number (M := M) (2 : ℂ)) ((_object_w74).val.right).wd.1 ((_object_w74).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_21118)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
                      let _atomic_wd_1_0 := _object_w75
                      exact h_21012)
                      litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                    )))))))
                )
            )

          have h_37058 :=
            (And.left h_21013)

          have h_37059 :=
            (And.left (And.right h_21013))

          have h_37060 :=
            (And.right (And.right h_21013))

          have h_37061 :=
            h_37058

          have h_37062 :=
            h_37059

          have h_37063 :=
            h_37060

          have h_37064 :=
            (Eq.trans h_37058 h_37059)

          have h_37065 :=
            (Eq.trans (Eq.trans h_37058 h_37059) h_37060)

          have h_37066 :=
            (Eq.trans h_37059 h_37060)
          exact h_37065
        )
      )
  )

theorem h_37176 : ∀ {_Host_i18 : Type v18} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_37186 : Litex.In _value_i18 (Litex.Q (M := M))) {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_37187 : Litex.In _value_i19 (Litex.Q (M := M))) (h_37172 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ))) (h_37173 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ))) (h_37174 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37186 h_37172)
  let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37187 h_37173)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), Litex.Same _value_i18 _value_i19 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i18 _rep_i18 _value_i18 h_37186 _Host_i19 _rep_i19 _value_i19 h_37187 h_37172 h_37173 h_37174
          have h_37213 : Litex.In _value_i18 (Litex.Q (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_37186
                )
            )
          have h_37214 : Litex.In _value_i19 (Litex.Q (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_37187
                )
            )
          have h_37177 : (by
            have h_37240 : Litex.In _value_i18 (Litex.Q (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_37213
                  )
              )
            have h_37241 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_37172
                  )
              )
            exact (by
              let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172);
              (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  have h_37373 : Litex.In _value_i18 (Litex.Q (M := M)) :=
                    h_37240
                  have h_37378 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
                    h_37241
                  exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i18)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i18 h_37373 h_37378))
                ))))
              exact Litex.Same _equal_wd_1_0 _value_i18)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_37240 : Litex.In _value_i18 (Litex.Q (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_37213
                          )
                      )
                    have h_37241 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_37172
                          )
                      )
                    have h_37242 : Litex.Same (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172);
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        have h_37373 : Litex.In _value_i18 (Litex.Q (M := M)) :=
                          h_37240
                        have h_37378 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
                          h_37241
                        exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i18)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i18 h_37373 h_37378))
                      )))) _value_i18 :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((h_10318 (M := M)) _value_i18 h_37240 h_37241)
                          )
                      )
                    exact (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172);
                  (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      have h_37373 : Litex.In _value_i18 (Litex.Q (M := M)) :=
                        h_37240
                      have h_37378 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
                        h_37241
                      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i18)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i18 h_37373 h_37378))
                    ))));
                  (show Litex.Same _equal_wd_1_0 _value_i18 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_37242).trans (Litex.sameRefl _value_i18)))))
                  )
                )
            )
          have h_37178 : (by
            have h_37494 : Litex.In _value_i19 (Litex.Q (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_37214
                  )
              )
            have h_37495 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_37173
                  )
              )
            exact (by
              let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173);
              (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  have h_37631 : Litex.In _value_i19 (Litex.Q (M := M)) :=
                    h_37494
                  have h_37636 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
                    h_37495
                  exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i19)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i19 h_37631 h_37636))
                ))))
              exact Litex.Same _equal_wd_1_0 _value_i19)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_37494 : Litex.In _value_i19 (Litex.Q (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_37214
                          )
                      )
                    have h_37495 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_37173
                          )
                      )
                    have h_37496 : Litex.Same (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173);
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        have h_37631 : Litex.In _value_i19 (Litex.Q (M := M)) :=
                          h_37494
                        have h_37636 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
                          h_37495
                        exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i19)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i19 h_37631 h_37636))
                      )))) _value_i19 :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((h_10318 (M := M)) _value_i19 h_37494 h_37495)
                          )
                      )
                    exact (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173);
                  (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      have h_37631 : Litex.In _value_i19 (Litex.Q (M := M)) :=
                        h_37494
                      have h_37636 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
                        h_37495
                      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i19)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i19 h_37631 h_37636))
                    ))));
                  (show Litex.Same _equal_wd_1_0 _value_i19 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_37496).trans (Litex.sameRefl _value_i19)))))
                  )
                )
            )
          have h_37179 : (by
            let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
                    exact (by
                      have h_37787 : Litex.In _value_i18 (Litex.Q (M := M)) :=
                        h_37213
                      have h_37792 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
                        h_37172
                      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i18)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i18 h_37787 h_37792))
                    ))
                )
            )
          let _object_w95 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.rationalToComplex (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172) (Litex.callInOutput (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)))) (Litex.numberInC (M := M) (2 : ℂ))))

          have h_37180 : (by
            let _atomic_wd_1_0 := _object_w95
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w95
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172);
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.Q from (Litex.callInOutput _litex_numeric_call)));
                    _litex_numeric_member) (Litex.numberInC (M := M) (2 : ℂ)) (by
                      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                      exact h_37179)) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          have h_37181 : (by
            let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
                    exact (Litex.notSameOfSame (_object_w95).val.left _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_37174 (show @Eq M.Value _ _ from Eq.refl _) h_37179))
                )
            )
          let _object_w97 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.rationalToComplex (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173) (Litex.callInOutput (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)))) (Litex.numberInC (M := M) (2 : ℂ))))

          have h_37182 : (by
            let _atomic_wd_1_0 := _object_w97
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w97
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173);
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.Q from (Litex.callInOutput _litex_numeric_call)));
                    _litex_numeric_member) (Litex.numberInC (M := M) (2 : ℂ)) (by
                      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                      exact (Litex.notSameOfSame (_object_w95).val.left _atomic_wd_2_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_37174 (show @Eq M.Value _ _ from Eq.refl _) h_37179))) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          let _object_w98 := (let _wd_1_0 := (let _wd_2_0 := (_object_w95).val.left;
          let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.rationalToComplex (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172) (Litex.callInOutput (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)))) (Litex.numberInC (M := M) (1 : ℂ))));
          let _wd_1_1 := _object_w95;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.addInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
            let _atomic_wd_1_0 := _object_w95
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.subInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
            let _atomic_wd_1_0 := _object_w95
            exact h_37180)))

          have h_37183 : (by
            let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172);
            (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                have h_37484 : Litex.In _value_i18 (Litex.Q (M := M)) :=
                  h_37213
                have h_37489 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
                  h_37172
                exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i18)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i18 h_37484 h_37489))
              ))))
            let _equal_wd_1_1 := _object_w98
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172);
                  (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      have h_37484 : Litex.In _value_i18 (Litex.Q (M := M)) :=
                        h_37213
                      have h_37489 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
                        h_37172
                      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i18)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i18 h_37484 h_37489))
                    ))));
                  let _equal_wd_1_1 := _object_w98;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (2 : ℂ)))) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (2 : ℂ)))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (2 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (2 : ℂ)))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                    let _wd_1_1 := ((_equal_wd_1_1).val.left).val.left;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (by
                        let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact h_37179)))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1039 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (2 : ℂ)))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w99 := (let _wd_1_0 := (let _wd_2_0 := (_object_w97).val.left;
          let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.rationalToComplex (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173) (Litex.callInOutput (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)))) (Litex.numberInC (M := M) (1 : ℂ))));
          let _wd_1_1 := _object_w97;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.addInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
            let _atomic_wd_1_0 := _object_w97
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.subInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
            let _atomic_wd_1_0 := _object_w97
            exact h_37182)))

          have h_37184 : (by
            let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173);
            (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                have h_37742 : Litex.In _value_i19 (Litex.Q (M := M)) :=
                  h_37214
                have h_37749 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
                  h_37173
                exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i19)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i19 h_37742 h_37749))
              ))))
            let _equal_wd_1_1 := _object_w99
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173);
                  (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      have h_37742 : Litex.In _value_i19 (Litex.Q (M := M)) :=
                        h_37214
                      have h_37749 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
                        h_37173
                      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i19)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i19 h_37742 h_37749))
                    ))));
                  let _equal_wd_1_1 := _object_w99;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ)))) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ)))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ)))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                    let _wd_1_1 := ((_equal_wd_1_1).val.left).val.left;
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (by
                        let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.notSameOfSame ((_object_w98).val.left).val.left _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_37174 (show @Eq M.Value _ _ from Eq.refl _) h_37179))))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1039 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.divValue (M.addValue _raw_i8 (M.number (1 : ℂ))) (M.subValue _raw_i8 (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ)))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_37185 : (by
            let _chain_wd_37185_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172);
            (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                have h_37484 : Litex.In _value_i18 (Litex.Q (M := M)) :=
                  h_37213
                have h_37489 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
                  h_37172
                exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i18)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i18 h_37484 h_37489))
              ))))
            let _chain_wd_37185_2 := _chain_wd_37185_1
            let _chain_wd_37185_3 := _object_w98
            let _chain_wd_37185_4 := _object_w98
            let _chain_wd_37185_5 := _object_w99
            let _chain_wd_37185_6 := _object_w99
            let _chain_wd_37185_7 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173);
            (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                have h_37742 : Litex.In _value_i19 (Litex.Q (M := M)) :=
                  h_37214
                have h_37749 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
                  h_37173
                exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i19)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i19 h_37742 h_37749))
              ))))
            let _chain_wd_37185_8 := _chain_wd_37185_7
            exact ((by
              let _equal_wd_1_1 := _chain_wd_37185_1
              exact Litex.Same _value_i18 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_37185_2
              let _equal_wd_1_1 := _chain_wd_37185_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_37185_4
              let _equal_wd_1_1 := _chain_wd_37185_5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_37185_6
              let _equal_wd_1_1 := _chain_wd_37185_7
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_37185_8
              exact Litex.Same _equal_wd_1_0 _value_i19)))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_37185_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172);
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i18 (h_627 (M := M)) h_37213 h_37172)
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        have h_37484 : Litex.In _value_i18 (Litex.Q (M := M)) :=
                          h_37213
                        have h_37489 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
                          h_37172
                        exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i18)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i18 h_37484 h_37489))
                      ))))
                    let _chain_wd_37185_2 := _chain_wd_37185_1
                    let _chain_wd_37185_3 := _object_w98
                    let _chain_wd_37185_4 := _object_w98
                    let _chain_wd_37185_5 := _object_w99
                    let _chain_wd_37185_6 := _object_w99
                    let _chain_wd_37185_7 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173);
                    (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (2 : ℂ))))) (_object_i7 (M := M)) _wd_1_0 (h_1038 (M := M)) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (1 : ℂ))))) (_object_i4 (M := M)) _value_i19 (h_627 (M := M)) h_37214 h_37173)
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Q (M := M))) (Litex.callInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        have h_37742 : Litex.In _value_i19 (Litex.Q (M := M)) :=
                          h_37214
                        have h_37749 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
                          h_37173
                        exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (Litex.sameRefl _value_i19)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((h_1042 (M := M)) _value_i19 h_37742 h_37749))
                      ))))
                    let _chain_wd_37185_8 := _chain_wd_37185_7
                    exact (And.intro (h_37177).symm (And.intro h_37183 (And.intro (congrArg₂ M.divValue (show (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (1 : ℂ))) = (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (1 : ℂ))) from (congrArg₂ M.addValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) from h_37174) (show (M.number (1 : ℂ)) = (M.number (1 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) (M.number (2 : ℂ))) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ))) from (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i18)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) from h_37174) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))))) (And.intro (h_37184).symm h_37178)))))
                )
            )

          have h_44872 :=
            (And.left h_37185)

          have h_44873 :=
            (And.left (And.right h_37185))

          have h_44874 :=
            (And.left (And.right (And.right h_37185)))

          have h_44875 :=
            (And.left (And.right (And.right (And.right h_37185))))

          have h_44876 :=
            (And.right (And.right (And.right (And.right h_37185))))

          have h_44877 :=
            h_44872

          have h_44878 :=
            h_44873

          have h_44879 :=
            h_44874

          have h_44880 :=
            h_44875

          have h_44881 :=
            h_44876

          have h_44882 :=
            (Eq.trans h_44872 h_44873)

          have h_44883 :=
            (Eq.trans (Eq.trans h_44872 h_44873) h_44874)

          have h_44884 :=
            (Eq.trans (Eq.trans (Eq.trans h_44872 h_44873) h_44874) h_44875)

          have h_44885 :=
            (Eq.trans (Eq.trans (Eq.trans (Eq.trans h_44872 h_44873) h_44874) h_44875) h_44876)

          have h_44886 :=
            (Eq.trans h_44873 h_44874)

          have h_44887 :=
            (Eq.trans (Eq.trans h_44873 h_44874) h_44875)

          have h_44888 :=
            (Eq.trans (Eq.trans (Eq.trans h_44873 h_44874) h_44875) h_44876)

          have h_44889 :=
            (Eq.trans h_44874 h_44875)

          have h_44890 :=
            (Eq.trans (Eq.trans h_44874 h_44875) h_44876)

          have h_44891 :=
            (Eq.trans h_44875 h_44876)
          exact h_44885
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_inverse_x5f_maps_x2f_statement_x2e_lit
