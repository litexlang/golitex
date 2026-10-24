import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sketch_x5f_in_x5f_named_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same _value_i1 _value_i1 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4
          have h_5 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have : True := by
            let _object_w3 := (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5) (Litex.numberInC (M := M) (0 : ℂ)))

            have h_3 : (by
              let _equal_wd_1_0 := _object_w3
              exact Litex.Same _equal_wd_1_0 _value_i1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w3;
                    (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_5)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_5)) (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_5)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_5)) (by ring!))))
                  )
              )
            exact True.intro
          exact (show @Eq M.Value _ _ from Eq.refl _)
        )
      )
  )

include M in
private theorem _sketch_2 : True := by
  have h_24 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

  obtain ⟨_witness_i3, _member_i3⟩ := h_24

  let _value_i3 := Litex.semanticObject (M := M) _witness_i3 (M.member_isSet _member_i3)

  have h_25 : Litex.In _value_i3 (Litex.R (M := M)) := _member_i3
  have h_23 : Litex.Same _value_i3 _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (by
            have h_26 : Litex.In _value_i3 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_25
                  )
              )
            have h_27 : Litex.Same _value_i3 _value_i3 :=
              (by
                litex_checked_step =>
                  exact (
                    ((h_2 (M := M)) _value_i3 h_26)
                  )
              )
            exact (((Litex.sameRefl _value_i3)).symm.trans ((h_27).trans (Litex.sameRefl _value_i3)))
          )
        )
    )
  exact True.intro

theorem h_32 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_33 : Litex.In _value_i4 (Litex.R (M := M)))

include M in
private theorem _sketch_4 {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_33 : Litex.In _value_i4 (Litex.R (M := M))) : True := by
  have h_34 : Litex.Same _value_i4 _value_i4 :=
    (by
      litex_checked_step =>
        exact (
          (by
            have h_35 : Litex.In _value_i4 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_33
                  )
              )
            have h_36 : Litex.Same _value_i4 _value_i4 :=
              (by
                litex_checked_step =>
                  exact (
                    ((h_2 (M := M)) _value_i4 h_35)
                  )
              )
            exact (((Litex.sameRefl _value_i4)).symm.trans ((h_36).trans (Litex.sameRefl _value_i4)))
          )
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_sketch_x5f_in_x5f_named_x5f_theorem_x2f_statement_x2e_lit
