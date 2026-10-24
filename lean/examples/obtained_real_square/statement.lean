import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_obtained_x5f_real_x5f_square_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_1 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M)))

theorem h_4 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_5 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i2 _value_i2 (M.real_subset_complex _ h_5) (M.real_subset_complex _ h_5)) (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_2)) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)
          have h_65 : Litex.In _value_i2 (Litex.R (M := M)) := h_2
          have h_66 : Litex.Same _value_i2 _value_i1 := rfl
          have h_67 : (by
            let _equal_wd_1_0 := (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ (Litex.inOfSame _value_i2 _value_i1 (Litex.R (M := M)) (Litex.R (M := M)) h_66 (show @Eq M.Value _ _ from Eq.refl _) h_65)) (M.real_subset_complex _ (Litex.inOfSame _value_i2 _value_i1 (Litex.R (M := M)) (Litex.R (M := M)) h_66 (show @Eq M.Value _ _ from Eq.refl _) h_65)))
            let _equal_wd_1_1 := _equal_wd_1_0
            exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ⟨_value_i2, h_65, h_67⟩
      )
  )

noncomputable def _value_i4 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_135 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135)) (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_2)) from (h_4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)))

theorem h_190 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.In (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_135 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135)) (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_2)) from (h_4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))))))
      )
  )

theorem h_191 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.Same ((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_135 : Litex.In _value_i3 (Litex.R (M := M))) => (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135))) (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) ((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_135 : Litex.In _value_i3 (Litex.R (M := M))) => (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_2))) (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_135 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135)) (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_2)) from (h_4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))))))
      )
  )

noncomputable def _object_w8 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) := (let _wd_1_0 := (Litex.div (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_1_1 := _wd_1_0;
(Litex.mul _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.divInC (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) (Litex.numberInC (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.2.2)) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.divInC (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) (Litex.numberInC (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.2.2))))

noncomputable def _object_w9 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) := (let _wd_1_0 := ((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_135 : Litex.In _value_i3 (Litex.R (M := M))) => (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135))) (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2));
let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.mulInC (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (M.real_subset_complex _ (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) (M.real_subset_complex _ (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_192 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : (by
  let _equal_wd_1_0 := (_object_w8 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
  let _equal_wd_1_1 := (_object_w9 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w8 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2);
        let _equal_wd_1_1 := (_object_w9 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2);
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.realToComplex (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) / (2 : ℂ)) * ((Litex.NativeBridge.asComplex (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.realToComplex (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) / (2 : ℂ))) ((((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_135 : Litex.In _value_i3 (Litex.R (M := M))) => (let _obtained_object := (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135));
        show { _z : ℂ // Litex.denote _obtained_object = M.number _z ∧ Litex.In _obtained_object Litex.C } from ⟨((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_135)) * (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_135))), (Litex.NativeBridge.denoteMul _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135) _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_135)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_135))), (Litex.mulInC _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135))⟩)) (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))).val / (4 : ℂ)) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2.1 ((_equal_wd_1_0).val.left).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.realToComplex (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.right).wd.1 ((_equal_wd_1_0).val.right).wd.2.1 ((_equal_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.realToComplex (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_135 : Litex.In _value_i3 (Litex.R (M := M))) => (let _obtained_object := (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135));
        show { _z : ℂ // Litex.denote _obtained_object = M.number _z ∧ Litex.In _obtained_object Litex.C } from ⟨((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_135)) * (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_135))), (Litex.NativeBridge.denoteMul _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135) _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_135)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_135))), (Litex.mulInC _value_i3 _value_i3 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_135))⟩)) (_value_i4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (h_190 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))).property.1 (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (by
          have _litex_nz_0 : ((2 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
          have _litex_nz_1 : ((4 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (4 : ℂ)) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
        ))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_obtained_x5f_real_x5f_square_x2f_statement_x2e_lit
