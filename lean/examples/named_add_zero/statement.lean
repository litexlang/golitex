import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_add_x5f_zero_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem named_thm_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 _h_param_i1) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1
    exact (Litex.NativeBridge.sameOfDenoteNumber (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 _h_param_i1) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 _h_param_i1)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 _h_param_i1)) (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 _h_param_i1) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 _h_param_i1)) (0 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 _h_param_i1)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 _h_param_i1)) (by ring))
  )

noncomputable def _object_i3 := (Litex.number (M := M) (2 : ℂ))

noncomputable def _object_i4 := (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) (Litex.numberInC (M := M) (0 : ℂ)))

theorem fact_4 : Litex.Same (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) (Litex.numberInC (M := M) (0 : ℂ))) (_object_i3 (M := M)) :=
  (((Litex.sameRefl (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) (Litex.numberInC (M := M) (0 : ℂ))))).symm.trans ((((named_thm_1 (M := M)) (_object_i3 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))))).trans (Litex.sameRefl (_object_i3 (M := M)))))

theorem fact_5 : Litex.Same (_object_i4 (M := M)) (_object_i3 (M := M)) :=
  (((((Litex.sameRefl (_object_i4 (M := M)))).trans (Litex.sameRefl (Litex.add (_object_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i3 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))) (Litex.numberInC (M := M) (0 : ℂ)))))).trans (fact_4 (M := M)))

noncomputable def _object_i5 := (_object_i3 (M := M))

theorem fact_7 : Litex.Same (Litex.add (_object_i5 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i5 (M := M)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i5 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl (_object_i3 (M := M)))).trans ((Litex.sameRefl (_object_i3 (M := M)))).symm) (Litex.sameRefl (Litex.R (M := M))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))))) (Litex.numberInC (M := M) (0 : ℂ))) (_object_i5 (M := M)) :=
  (((Litex.sameRefl (Litex.add (_object_i5 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex (_object_i5 (M := M)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i5 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl (_object_i3 (M := M)))).trans ((Litex.sameRefl (_object_i3 (M := M)))).symm) (Litex.sameRefl (Litex.R (M := M))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))))) (Litex.numberInC (M := M) (0 : ℂ))))).symm.trans ((((named_thm_1 (M := M)) (_object_i5 (M := M)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i5 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl (_object_i3 (M := M)))).trans ((Litex.sameRefl (_object_i3 (M := M)))).symm) (Litex.sameRefl (Litex.R (M := M))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))))).trans (Litex.sameRefl (_object_i5 (M := M)))))
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_add_x5f_zero_x2f_statement_x2e_lit
