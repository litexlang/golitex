import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_calls_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_53 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_54 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

include M in
private theorem _sketch_2 : True := by
  let _object_i3 := (Litex.number (M := M) (4 : ℂ))
  have h_60 : Litex.In _object_i3 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
        )
    )
  have h_61 : Litex.Same _object_i3 (Litex.number (M := M) (4 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.number (M := M) (4 : ℂ)))
        )
    )
  have h_72 : (by
    let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i3 (h_53 (M := M)) h_60 True.intro)
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i3 (h_53 (M := M)) h_60 True.intro);
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _object_i3)))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _object_i3)) = (M.addValue (Litex.denote _object_i3) (M.number (1 : ℂ))) from by
            let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i3 (h_53 (M := M)) h_60 True.intro)
            let _litex_formula := (_object_i1 (M := M))
            have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_54 (M := M))
            have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
            have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
            exact _litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (Litex.denote _object_i3) (M.number (1 : ℂ))) from rfl))
          )).trans (((congrArg₂ M.addValue h_61 (Eq.refl (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (4 : ℂ)) (M.number (1 : ℂ))) = M.number (5 : ℂ) from ((congrArg₂ M.addValue (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (4 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (5 : ℂ)))).symm)))
        )
    )
  have h_55 : (by
    let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i3 (h_53 (M := M)) h_60 True.intro)
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          h_72
        )
    )
  exact True.intro

noncomputable def _object_i4 := (Litex.number (M := M) (7 : ℂ))
theorem h_79 : Litex.Same (_object_i4 (M := M)) (Litex.number (M := M) (7 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (7 : ℂ)))
      )
  )

theorem h_1500 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (_object_i4 (M := M)) (h_53 (M := M)) (Litex.inOfSame (Litex.number (M := M) (7 : ℂ)) (_object_i4 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) ((h_79 (M := M))).symm (Litex.sameRefl (Litex.R (M := M))) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (8 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (_object_i4 (M := M)) (h_53 (M := M)) (Litex.inOfSame (Litex.number (M := M) (7 : ℂ)) (_object_i4 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) ((h_79 (M := M))).symm (Litex.sameRefl (Litex.R (M := M))) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))) True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (8 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (8 : ℂ)) from (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i4 (M := M)))))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i4 (M := M)))) = (M.addValue (Litex.denote (_object_i4 (M := M))) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (_object_i4 (M := M)) (h_53 (M := M)) (Litex.inOfSame (Litex.number (M := M) (7 : ℂ)) (_object_i4 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) ((h_79 (M := M))).symm (Litex.sameRefl (Litex.R (M := M))) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))) True.intro)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_54 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact _litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (Litex.denote (_object_i4 (M := M))) (M.number (1 : ℂ))) from rfl))
        )).trans (((congrArg₂ M.addValue (h_79 (M := M)) (Eq.refl (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (7 : ℂ)) (M.number (1 : ℂ))) = M.number (8 : ℂ) from ((congrArg₂ M.addValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (7 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ))).trans (congrArg M.number (by norm_num : (8 : ℂ) = (8 : ℂ)))).symm)))
      )
  )

theorem h_2211 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (_object_i4 (M := M)) (h_53 (M := M)) (Litex.inOfSame (Litex.number (M := M) (7 : ℂ)) (_object_i4 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) ((h_79 (M := M))).symm (Litex.sameRefl (Litex.R (M := M))) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (8 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_1500 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_calls_x2f_statement_x2e_lit
