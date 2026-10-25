import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_tangent_x5f_quotient_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : (by
  let _atomic_wd_1_0 := (Litex.cos _value_i1 h_16)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))), (by
  let _object_w4 := (Litex.tan _value_i1 h_16 (by
    let _atomic_wd_1_0 := (Litex.cos _value_i1 h_16)
    exact h_1))
  let _object_w5 := (let _wd_1_0 := (Litex.sin _value_i1 h_16);
  let _wd_1_1 := (Litex.cos _value_i1 h_16);
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.sin _value_i1 h_16)
    exact (M.real_subset_complex _ (Litex.sinInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (Litex.cosInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact h_1)))
  exact (by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
          let _object_w4 := (Litex.tan _value_i1 h_16 (by
            let _atomic_wd_1_0 := (Litex.cos _value_i1 h_16)
            exact h_1))
          let _object_w5 := (let _wd_1_0 := (Litex.sin _value_i1 h_16);
          let _wd_1_1 := (Litex.cos _value_i1 h_16);
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.sin _value_i1 h_16)
            exact (M.real_subset_complex _ (Litex.sinInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (Litex.cosInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_1)))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.tan ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16))).re : ℂ) ((Real.sin ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16))).re : ℂ) / (Real.cos ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16))).re : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteTan _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16)) _trig.wd.1 (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_16)))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (let _trig := (_equal_wd_1_1).val.left; Litex.denoteSin _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_16)))) (let _trig := (Litex.cos _value_i1 h_16); Litex.denoteCos _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_16))))) (by exact Litex.tanQuotient ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_16))).re))))
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_tangent_x5f_quotient_x2f_statement_x2e_lit
