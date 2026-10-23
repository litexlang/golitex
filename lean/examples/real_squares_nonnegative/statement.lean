import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_squares_x5f_nonnegative_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w3 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_15 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact (by
    let _atomic_wd_1_1 := _object_w3
    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15
    let _object_w3 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_15 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    have h_1 : (by
      let _atomic_wd_1_1 := _object_w3
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_1 := _object_w3
              exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_1_1 h_15 (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num)))
          )
      )
    exact h_1
  )

theorem h_265 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_279 : Litex.In _value_i2 (Litex.R (M := M))), (by
  let _object_w5 := (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_279 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact (by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0)
) :=
  (by
    intro _Host_i2 _rep_i2 _value_i2 h_279
    let _object_w5 := (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_279 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    have h_264 : (by
      let _atomic_wd_1_0 := _object_w5
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w5
              exact (by
                let _atomic_wd_2_1 := _atomic_wd_1_0
                exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_2_1 h_279 (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num))))
          )
      )
    exact h_264
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_squares_x5f_nonnegative_x2f_statement_x2e_lit
