import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_number_x5f_theory_x5f_values_x2f_statement_x2e_lit

universe u v2
variable {M : Litex.Semantics.{u}}

theorem h_1 : Litex.Prime (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.prime_iff_of_denote (Litex.number (M := M) (5 : ℂ)) (5 : ℕ) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).mpr (by norm_num))
      )
  )

theorem h_6 : ¬ Litex.Prime (Litex.number (M := M) (9 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((not_congr (Litex.prime_iff_of_denote (Litex.number (M := M) (9 : ℂ)) (9 : ℕ) (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num : (9 : ℂ) = ((9 : ℕ) : ℂ)))))).mpr (by norm_num))
      )
  )

theorem h_8 : Litex.Coprime (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (15 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.coprime_iff_of_denote (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (15 : ℂ)) (8 : ℕ) (15 : ℕ) (((Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ))).trans (congrArg M.number (by norm_num : (8 : ℂ) = ((8 : ℕ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num : (15 : ℂ) = ((15 : ℕ) : ℂ))))).mpr (by norm_num [Nat.Coprime]))
      )
  )

theorem h_15 : ¬ Litex.Coprime (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (12 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((not_congr (Litex.coprime_iff_of_denote (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (8 : ℕ) (12 : ℕ) (((Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ))).trans (congrArg M.number (by norm_num : (8 : ℂ) = ((8 : ℕ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = ((12 : ℕ) : ℂ)))))).mpr (by norm_num [Nat.Coprime]))
      )
  )

theorem h_20 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.In _value_i2 (Litex.N (M := M))) (h_18 : Litex.Prime _value_i2), Litex.Prime _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_21 h_18
          have h_22 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_21)
                )
            )
          have h_33 : Litex.In _value_i2 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_21
                )
            )
          have h_34 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_33)
                )
            )
          exact h_18
        )
      )
  )

theorem h_58 : Litex.Prime (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_59 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num))
                )
            )
          have h_62 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (5 : ℂ)) h_59)
                )
            )
          have h_60 : Litex.Prime (Litex.number (M := M) (5 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_1 (M := M))
                )
            )
          have h_61 : Litex.Prime (Litex.number (M := M) (5 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_20 (M := M)) (Litex.number (M := M) (5 : ℂ)) h_59 h_60)
                )
            )
          exact h_61
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_number_x5f_theory_x5f_values_x2f_statement_x2e_lit
