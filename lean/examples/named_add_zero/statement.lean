import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_add_x5f_zero_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_17) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_17
    exact (Litex.NativeBridge.sameOfDenoteNumber (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_17) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_17)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_17)) (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_17) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_17)) (0 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_17)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_17)) (by ring))
  )

noncomputable def _object_i3 := (Litex.number (M := M) (2 : ℂ))
theorem h_49 : Litex.In (_object_i3 (M := M)) (Litex.R (M := M)) :=
  (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))
theorem h_50 : Litex.Same (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))

noncomputable def _object_i4 := (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (h_49 (M := M))) (Litex.numberInC (M := M) (0 : ℂ)))
theorem h_64 : Litex.Same (_object_i4 (M := M)) (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (h_49 (M := M))) (Litex.numberInC (M := M) (0 : ℂ))) :=
  (Litex.sameRefl (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (h_49 (M := M))) (Litex.numberInC (M := M) (0 : ℂ))))

theorem h_65 : Litex.Same (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (h_49 (M := M))) (Litex.numberInC (M := M) (0 : ℂ))) (_object_i3 (M := M)) :=
  (by
    have h_66 : Litex.In (_object_i3 (M := M)) (Litex.R (M := M)) :=
      (h_49 (M := M))
    have h_67 : Litex.Same (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (h_49 (M := M))) (Litex.numberInC (M := M) (0 : ℂ))) (_object_i3 (M := M)) :=
      ((h_2 (M := M)) (_object_i3 (M := M)) h_66)
    exact (((Litex.sameRefl (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (h_49 (M := M))) (Litex.numberInC (M := M) (0 : ℂ))))).symm.trans ((h_67).trans (Litex.sameRefl (_object_i3 (M := M)))))
  )

theorem h_72 : Litex.Same (_object_i4 (M := M)) (_object_i3 (M := M)) :=
  (((((Litex.sameRefl (_object_i4 (M := M)))).trans (h_64 (M := M)))).trans (h_65 (M := M)))

noncomputable def _object_i5 := (_object_i3 (M := M))
theorem h_74 : Litex.Same (_object_i5 (M := M)) (_object_i3 (M := M)) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_75 : (let h_76 : Litex.In (_object_i5 (M := M)) (Litex.R (M := M)) :=
  (Litex.inOfSame (_object_i3 (M := M)) (_object_i5 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl (_object_i3 (M := M)))).trans ((h_74 (M := M))).symm) (Litex.sameRefl (Litex.R (M := M))) (h_49 (M := M)));
Litex.Same (Litex.add (_object_i5 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i5 (M := M)) h_76) (Litex.numberInC (M := M) (0 : ℂ))) (_object_i5 (M := M))) :=
  (by
    have h_76 : Litex.In (_object_i5 (M := M)) (Litex.R (M := M)) :=
      (Litex.inOfSame (_object_i3 (M := M)) (_object_i5 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl (_object_i3 (M := M)))).trans ((h_74 (M := M))).symm) (Litex.sameRefl (Litex.R (M := M))) (h_49 (M := M)))
    have h_77 : Litex.Same (Litex.add (_object_i5 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i5 (M := M)) h_76) (Litex.numberInC (M := M) (0 : ℂ))) (_object_i5 (M := M)) :=
      ((h_2 (M := M)) (_object_i5 (M := M)) h_76)
    exact (((Litex.sameRefl (Litex.add (_object_i5 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i5 (M := M)) h_76) (Litex.numberInC (M := M) (0 : ℂ))))).symm.trans ((h_77).trans (Litex.sameRefl (_object_i5 (M := M)))))
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_add_x5f_zero_x2f_statement_x2e_lit
