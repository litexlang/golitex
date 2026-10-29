import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_numeric_x5f_set_x5f_builder_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (Litex.RPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_163 : Litex.In _value_i2 (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_16 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
  have h_17 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_16)).choose
        )
    )
  exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.abs _value_i3 h_17)) ∧ (Litex.Lt (Litex.abs _value_i3 h_17) _value_i1))
)))), Litex.In _value_i2 (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10 _Host_i2 _rep_i2 _value_i2 h_163
          have h_11 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i1 h_10)
                )
            )
          have h_12 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_11)
                )
            )
          have h_13 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_11) _litex_zero.symm)
                )
            )
          have h_164 : (M.mem (Litex.denote _value_i2) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i4 : M.Value) => ∃ (_ : M.mem _raw_i4 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i4 = (M.number (0 : ℂ))))))) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_16 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
                    have h_17 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_16)).choose
                          )
                      )
                    exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.abs _value_i3 h_17)) ∧ (Litex.Lt (Litex.abs _value_i3 h_17) _value_i1))
                  ))); (Litex.inSetBuilderObj_iff _value_i2 _litex_builder).mp h_163)).choose
                )
            )
          have h_167 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (Litex.denote _value_i2)) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (Litex.denote _value_i2)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i1) = M.number (_s : ℂ) ∧ _r < _s))) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_16 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
                    have h_17 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_16)).choose
                          )
                      )
                    exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.abs _value_i3 h_17)) ∧ (Litex.Lt (Litex.abs _value_i3 h_17) _value_i1))
                  ))); (Litex.inSetBuilderObj_iff _value_i2 _litex_builder).mp h_163)).choose_spec
                )
            )
          have h_165 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_16 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_17 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_16)).choose
                  )
              )
            have h_18 : (¬ ((Litex.denote _value_i3) = (M.number (0 : ℂ)))) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_16)).choose_spec
                  )
              )
            exact (Litex.abs _value_i3 h_17)
          )) (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)) h_164) :=
            (by
              litex_checked_step =>
                exact (
                  (And.left h_167)
                )
            )
          have h_166 : Litex.Lt ((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_16 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_17 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_16)).choose
                  )
              )
            have h_18 : (¬ ((Litex.denote _value_i3) = (M.number (0 : ℂ)))) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_16)).choose_spec
                  )
              )
            exact (Litex.abs _value_i3 h_17)
          )) (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)) h_164) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (And.right h_167)
                )
            )
          have h_173 : Litex.In _value_i1 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_326 : Litex.In _value_i2 (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_179 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_180 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_179)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.abs _value_i3 h_180)) ∧ (Litex.Lt (Litex.abs _value_i3 h_180) _value_i1))
          ))) :=
            (by
              litex_checked_step =>
                exact (
                  h_163
                )
            )
          have h_174 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i1 h_173)
                )
            )
          have h_175 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_174)
                )
            )
          have h_176 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_174) _litex_zero.symm)
                )
            )
          have h_327 : (M.mem (Litex.denote _value_i2) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i4 : M.Value) => ∃ (_ : M.mem _raw_i4 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i4 = (M.number (0 : ℂ))))))) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_179 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
                    have h_180 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_179)).choose
                          )
                      )
                    exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.abs _value_i3 h_180)) ∧ (Litex.Lt (Litex.abs _value_i3 h_180) _value_i1))
                  ))); (Litex.inSetBuilderObj_iff _value_i2 _litex_builder).mp h_326)).choose
                )
            )
          have h_330 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (Litex.denote _value_i2)) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (Litex.denote _value_i2)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i1) = M.number (_s : ℂ) ∧ _r < _s))) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_179 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
                    have h_180 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_179)).choose
                          )
                      )
                    exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.abs _value_i3 h_180)) ∧ (Litex.Lt (Litex.abs _value_i3 h_180) _value_i1))
                  ))); (Litex.inSetBuilderObj_iff _value_i2 _litex_builder).mp h_326)).choose_spec
                )
            )
          have h_328 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_179 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_180 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_179)).choose
                  )
              )
            have h_181 : (¬ ((Litex.denote _value_i3) = (M.number (0 : ℂ)))) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_179)).choose_spec
                  )
              )
            exact (Litex.abs _value_i3 h_180)
          )) (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)) h_327) :=
            (by
              litex_checked_step =>
                exact (
                  (And.left h_330)
                )
            )
          have h_329 : Litex.Lt ((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_179 : Litex.In _value_i3 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_180 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_179)).choose
                  )
              )
            have h_181 : (¬ ((Litex.denote _value_i3) = (M.number (0 : ℂ)))) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_177 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp h_179)).choose_spec
                  )
              )
            exact (Litex.abs _value_i3 h_180)
          )) (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)) h_327) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (And.right h_330)
                )
            )
          let _object_w16 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_331 : Litex.In _value_i5 (Litex.R (M := M))) => ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))))

          have h_8 : (by
            let _atomic_wd_1_1 := _object_w16
            exact Litex.In _value_i2 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w16
                    exact (Litex.inOfSame _value_i2 _value_i2 _atomic_wd_1_1 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left := _atomic_wd_1_1
                      let _right := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_327))
                )
            )

          have h_343 : (M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := _object_w16; (Litex.inSetBuilderObj_iff _value_i2 _litex_builder).mp h_8)).choose
                )
            )

          have h_344 : (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := _object_w16; (Litex.inSetBuilderObj_iff _value_i2 _litex_builder).mp h_8)).choose_spec
                )
            )
          have h_9 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_343
                )
            )
          exact h_343
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_numeric_x5f_set_x5f_builder_x2f_statement_x2e_lit
