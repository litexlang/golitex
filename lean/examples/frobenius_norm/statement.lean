import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_frobenius_x5f_norm_x2f_statement_x2e_lit

universe u v1 v2 v3 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_36 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)), (by
  let _object_w5 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_19 h_21 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
    exact h_36))
  exact (by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_21 _Host_i3 _rep_i3 _value_i3 h_36
          have h_20 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_19)
                )
            )
          have h_22 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_21)
                )
            )
          let _object_h37 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)))
          have h_37 : Litex.In _value_i3 _object_h37 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21) _object_h37 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21))) h_36)
                )
            )
          let _object_w5 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_19 h_21 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
            exact h_36))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (Litex.frobeniusNormInR _atomic_wd_1_0))
                )
            )
          exact h_1
        )
      )
  )

theorem h_77 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_94 : Litex.In _value_i6 (Litex.N (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_105 : Litex.In _value_i7 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) _value_i6 (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) h_94)), (by
  let _object_w11 := (Litex.frobeniusNorm _value_i7 (Litex.number (M := M) (0 : ℂ)) _value_i6 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) h_94 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) _value_i6 (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) h_94)
    exact h_105))
  exact (by
    let _atomic_wd_1_0 := _object_w11
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_94 _Host_i7 _rep_i7 _value_i7 h_105
          have h_95 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i6 h_94)
                )
            )
          let _object_h106 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) _value_i6 (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) h_94)))
          have h_106 : Litex.In _value_i7 _object_h106 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i7 _value_i7 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) _value_i6 (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) h_94) _object_h106 (Litex.sameRefl _value_i7) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) _value_i6 (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) h_94))) h_105)
                )
            )
          let _object_w11 := (Litex.frobeniusNorm _value_i7 (Litex.number (M := M) (0 : ℂ)) _value_i6 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) h_94 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) _value_i6 (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) h_94)
            exact h_105))
          have h_76 : (by
            let _atomic_wd_1_0 := _object_w11
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    exact (Litex.frobeniusNormInR _atomic_wd_1_0))
                )
            )
          exact h_76
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_frobenius_x5f_norm_x2f_statement_x2e_lit
