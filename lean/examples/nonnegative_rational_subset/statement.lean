import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonnegative_x5f_rational_x5f_subset_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_i1 := (Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2))
theorem h_92 : Litex.IsSet (_object_i1 (M := M)) :=
  (Litex.isSet (Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_48 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2)))
theorem h_93 : Litex.Same (_object_i1 (M := M)) (Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_48 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2)) :=
  (Litex.sameRefl (Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2)))

noncomputable def _object_i3 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_96 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4))
theorem h_179 : Litex.IsSet (_object_i3 (M := M)) :=
  (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_136 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4)))
theorem h_180 : Litex.Same (_object_i3 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_136 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4)) :=
  (Litex.sameRefl (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_96 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4)))

theorem h_181 : Litex.Subset (_object_i1 (M := M)) (_object_i3 (M := M)) :=
  (Litex.subsetOfSame (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_136 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4)) (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.sameRefl (_object_i1 (M := M))) ((((Litex.sameRefl (_object_i3 (M := M)))).trans (h_180 (M := M)))).symm (Litex.subsetOfForall (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_136 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4)) (by
    intro _Host_i7 _rep_i7 _value_i7 h_264
    have h_265 : Litex.In _value_i7 (Litex.Q (M := M)) :=
      (((Litex.inSetBuilder_iff _value_i7 ((Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_48 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_48 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame _value_i7 _value_i7 (_object_i1 (M := M)) (Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_48 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl _value_i7) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_93 (M := M))) h_264))).choose
    have h_266 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
      (((Litex.inSetBuilder_iff _value_i7 ((Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_48 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_48 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame _value_i7 _value_i7 (_object_i1 (M := M)) (Litex.setBuilder (Litex.Q (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_48 : Litex.In _value_i2 (Litex.Q (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl _value_i7) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_93 (M := M))) h_264))).choose_spec
    have h_251 : Litex.In _value_i7 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_136 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4)) :=
      (by
        let _set := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_136 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4))
        exact (Litex.inSetBuilder_iff _value_i7 _set.val.bound _set.val.predicate).mpr ⟨(Litex.rationalToReal _value_i7 h_265), h_266⟩)
    exact h_251
  )))
end LitexCompiled.file_lean_x2f_examples_x2f_nonnegative_x5f_rational_x5f_subset_x2f_statement_x2e_lit
