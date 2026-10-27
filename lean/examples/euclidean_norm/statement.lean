import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_euclidean_x5f_norm_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_26 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)), (by
  let _object_w5 := (Litex.euclideanNorm _value_i2 _value_i1 h_18 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
    exact h_26))
  exact (by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18 _Host_i2 _rep_i2 _value_i2 h_26
          have h_19 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_18)
                )
            )
          let _object_h27 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)))
          have h_27 : Litex.In _value_i2 _object_h27 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18) _object_h27 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)) h_26)
                )
            )
          let _object_w5 := (Litex.euclideanNorm _value_i2 _value_i1 h_18 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
            exact h_26))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (Litex.euclideanNormInR _atomic_wd_1_0))
                )
            )
          exact h_1
        )
      )
  )

theorem h_54 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_71 : Litex.In _value_i4 (Litex.N (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_79 : Litex.In _value_i5 (Litex.finiteSeq (Litex.C (M := M)) _value_i4 (Litex.isSet (Litex.C (M := M))) h_71)), (by
  let _object_w11 := (Litex.euclideanNorm _value_i5 _value_i4 h_71 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i4 (Litex.isSet (Litex.C (M := M))) h_71)
    exact h_79))
  exact (by
    let _atomic_wd_1_0 := _object_w11
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_71 _Host_i5 _rep_i5 _value_i5 h_79
          have h_72 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i4 h_71)
                )
            )
          let _object_h80 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i4 (Litex.isSet (Litex.C (M := M))) h_71)))
          have h_80 : Litex.In _value_i5 _object_h80 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i5 _value_i5 (Litex.finiteSeq (Litex.C (M := M)) _value_i4 (Litex.isSet (Litex.C (M := M))) h_71) _object_h80 (Litex.sameRefl _value_i5) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i4 (Litex.isSet (Litex.C (M := M))) h_71)) h_79)
                )
            )
          let _object_w11 := (Litex.euclideanNorm _value_i5 _value_i4 h_71 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i4 (Litex.isSet (Litex.C (M := M))) h_71)
            exact h_79))
          have h_53 : (by
            let _atomic_wd_1_0 := _object_w11
            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    exact (M.real_subset_complex _ (Litex.euclideanNormInR _atomic_wd_1_0)))
                )
            )
          exact h_53
        )
      )
  )

theorem h_107 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_134 : Litex.In _value_i7 (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))), (by
  let _object_w15 := (Litex.euclideanNorm _value_i7 (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
    exact h_134))
  exact (by
    let _atomic_wd_1_0 := _object_w15
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_134
          let _object_h135 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))))
          have h_135 : Litex.In _value_i7 _object_h135 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i7 _value_i7 (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))) _object_h135 (Litex.sameRefl _value_i7) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))) h_134)
                )
            )
          let _object_w15 := (Litex.euclideanNorm _value_i7 (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
            exact h_134))
          have h_106 : (by
            let _atomic_wd_1_0 := _object_w15
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w15
                    exact (Litex.euclideanNormInR _atomic_wd_1_0))
                )
            )
          exact h_106
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_euclidean_x5f_norm_x2f_statement_x2e_lit
