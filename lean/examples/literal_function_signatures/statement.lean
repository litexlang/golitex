import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_literal_x5f_function_x5f_signatures_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (M.addValue _raw_i1 (M.number (1 : ℂ)))) (by
  intro _raw_i1 h_15 _
  let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
  have h_15 : Litex.In _value_i1 (Litex.R (M := M)) := h_15
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_15) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_15) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i1 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))

noncomputable def _object_w4 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_53 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_53)
    have h_53 : Litex.In _value_i2 (Litex.R (M := M)) := h_53
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w3 (M := M))
  let _atomic_wd_1_1 := (_object_w4 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w3 (M := M))
          let _atomic_wd_1_1 := (_object_w4 (M := M))
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from by exact Litex.formulaFnInFnSet _atomic_wd_1_0))
      )
  )

noncomputable def _object_w10 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i3)) (by
  intro _raw_i3 h_98 h_54
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_98)
  have h_98 : Litex.In _value_i3 (Litex.R (M := M)) := h_98
  have h_54 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i3 = (M.number (0 : ℂ))))
            exact h_54)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_98) h_54)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_98) h_54)
    exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_98 (_atomic_wd_1_0).wd.2.2))))

noncomputable def _object_w11 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
    intro _raw_i4 h_161 h_55
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_161)
    have h_161 : Litex.In _value_i4 (Litex.R (M := M)) := h_161
    have h_55 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i4 = (M.number (0 : ℂ))))
              exact h_55)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))

theorem h_56 : (by
  let _atomic_wd_1_0 := (_object_w10 (M := M))
  let _atomic_wd_1_1 := (_object_w11 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w10 (M := M))
          let _atomic_wd_1_1 := (_object_w11 (M := M))
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from by exact Litex.formulaFnInFnSet _atomic_wd_1_0))
      )
  )

noncomputable def _object_w17 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 _raw_i7)) (by
  intro _raw_i6 _raw_i7 h_211 h_212 h_166
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_211)
  have h_211 : Litex.In _value_i6 (Litex.R (M := M)) := h_211
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_212)
  have h_212 : Litex.In _value_i7 (Litex.R (M := M)) := h_212
  have h_166 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i7 = (M.number (0 : ℂ))))
            exact h_166)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_211) (M.real_subset_complex _ h_212) h_166)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_211) (M.real_subset_complex _ h_212) h_166)
    exact (Litex.divInR _value_i6 _value_i7 h_211 h_212 (_atomic_wd_1_0).wd.2.2))))

noncomputable def _object_w18 := (let _checked_header : ∀ (_raw_i8 : M.Value) (_raw_i9 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i8 _raw_i9) → True := (by
    intro _raw_i8 _raw_i9 h_326 h_327 h_167
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_326)
    have h_326 : Litex.In _value_i8 (Litex.R (M := M)) := h_326
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_327)
    have h_327 : Litex.In _value_i9 (Litex.R (M := M)) := h_327
    have h_167 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i9 = (M.number (0 : ℂ))))
              exact h_167)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ)))))))

theorem h_168 : (by
  let _atomic_wd_1_0 := (_object_w17 (M := M))
  let _atomic_wd_1_1 := (_object_w18 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w17 (M := M))
          let _atomic_wd_1_1 := (_object_w18 (M := M))
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from by exact Litex.formulaFnInFnSet _atomic_wd_1_0))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_literal_x5f_function_x5f_signatures_x2f_statement_x2e_lit
