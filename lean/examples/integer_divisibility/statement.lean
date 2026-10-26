import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_divisibility_x2f_statement_x2e_lit

universe u v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.mod (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (0 : ℂ) (let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.modInZ _intop);
        (Litex.modDenoteInt _intop (15 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num : (15 : ℂ) = ((15 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

theorem h_6 : Litex.Dvd (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.dvdOfModZero (_object_w1 (M := M)) (h_1 (M := M)))
      )
  )

theorem h_14 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_15 : Litex.In _value_i2 (Litex.Z (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_16 : Litex.In _value_i3 (Litex.ZStar (M := M))) (h_12 : (by
  have h_17 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inZStar_nonzero _value_i3 h_16)
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.mod _value_i2 _value_i3 h_15 (Litex.inZStar_base _value_i3 h_16) h_17)
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
)), Litex.Dvd _value_i2 _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_15 _Host_i3 _rep_i3 _value_i3 h_16 h_12
          have h_17 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero _value_i3 h_16)
                )
            )
          have h_45 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_46 : Litex.In _value_i3 (Litex.ZStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_47 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero _value_i3 h_46)
                )
            )
          exact (Litex.dvdOfModZero (Litex.mod _value_i2 _value_i3 h_45 (Litex.inZStar_base _value_i3 h_46) h_47) h_12)
        )
      )
  )

theorem h_107 : Litex.Dvd (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_108 : Litex.In (Litex.number (M := M) (15 : ℂ)) (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num))
                )
            )
          have h_109 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.ZStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_intro (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) 0) (3 : ℂ) 0 (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) rfl (by norm_num [Complex.ext_iff])))
                )
            )
          have h_114 : ¬ Litex.Same (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero (Litex.number (M := M) (3 : ℂ)) h_109)
                )
            )
          have h_110 : (by
            let _equal_wd_1_0 := (_object_w1 (M := M))
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_1 (M := M))
                )
            )
          have h_111 : Litex.Dvd (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_14 (M := M)) (Litex.number (M := M) (15 : ℂ)) h_108 (Litex.number (M := M) (3 : ℂ)) h_109 h_110)
                )
            )
          exact h_111
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_divisibility_x2f_statement_x2e_lit
