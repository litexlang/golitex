import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_showcases_x2f_litex_x5f_to_x5f_lean_x5f_adapter_x2f_source_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w3 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_17));
  let _wd_1_1 := _value_i3;
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC _value_i1 _value_i2 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_17))) (M.real_subset_complex _ h_18) h_1))
  let _object_w4 := (let _wd_1_0 := (Litex.div _value_i1 _value_i3 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_18) h_1);
  let _wd_1_1 := (Litex.div _value_i2 _value_i3 (M.real_subset_complex _ h_17) (M.real_subset_complex _ h_18) h_1);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.divInC _value_i1 _value_i3 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_18) (_atomic_wd_1_0).wd.2.2)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.divInC _value_i2 _value_i3 (M.real_subset_complex _ h_17) (M.real_subset_complex _ h_18) (_atomic_wd_1_0).wd.2.2))))
  exact (let _equal_wd_1_0 := _object_w3;
  let _equal_wd_1_1 := _object_w4;
  Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 _Host_i3 _rep_i3 _value_i3 h_18 h_1
          let _object_w3 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_17));
          let _wd_1_1 := _value_i3;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i1 _value_i2 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_17))) (M.real_subset_complex _ h_18) h_1))
          let _object_w4 := (let _wd_1_0 := (Litex.div _value_i1 _value_i3 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_18) h_1);
          let _wd_1_1 := (Litex.div _value_i2 _value_i3 (M.real_subset_complex _ h_17) (M.real_subset_complex _ h_18) h_1);
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.divInC _value_i1 _value_i3 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_18) (_atomic_wd_1_0).wd.2.2)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.divInC _value_i2 _value_i3 (M.real_subset_complex _ h_17) (M.real_subset_complex _ h_18) (_atomic_wd_1_0).wd.2.2))))
          have h_2 : (let _equal_wd_1_0 := _object_w3;
          let _equal_wd_1_1 := _object_w4;
          Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  let _equal_wd_1_1 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16)) + (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_17))) / (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_18))) (((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16)) / (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_18))) + ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_17)) / (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_18)))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i1 _value_i2 ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_16)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_17))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_18))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteDiv _value_i1 _value_i3 ((_equal_wd_1_1).val.left).wd.1 ((_equal_wd_1_1).val.left).wd.2.1 ((_equal_wd_1_1).val.left).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_16)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_18))) (Litex.NativeBridge.denoteDiv _value_i2 _value_i3 ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2.1 ((_equal_wd_1_1).val.right).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_17)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_18)))) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_18)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i3 (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_18)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_18)) h_1
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_showcases_x2f_litex_x5f_to_x5f_lean_x5f_adapter_x2f_source_x2e_lit
