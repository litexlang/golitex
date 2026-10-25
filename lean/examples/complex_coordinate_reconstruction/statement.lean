import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_coordinate_x5f_reconstruction_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.re _value_i1 h_15);
  let _wd_1_1 := (let _wd_2_0 := (Litex.img _value_i1 h_15);
  let _wd_2_1 := (Litex.number (M := M) Complex.I);
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := (Litex.img _value_i1 h_15)
    exact (M.real_subset_complex _ (Litex.imgInR _atomic_wd_1_0))) (Litex.numberInC (M := M) Complex.I)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.re _value_i1 h_15)
    exact (M.real_subset_complex _ (Litex.reInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.img _value_i1 h_15);
    let _wd_2_1 := (Litex.number (M := M) Complex.I);
    (Litex.mul _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := (Litex.img _value_i1 h_15)
      exact (M.real_subset_complex _ (Litex.imgInR _atomic_wd_2_0))) (Litex.numberInC (M := M) Complex.I)))
    exact (Litex.mulInC (_atomic_wd_1_0).val.left (Litex.number (M := M) Complex.I) (M.real_subset_complex _ (Litex.imgInR (_atomic_wd_1_0).val.left)) (Litex.numberInC (M := M) Complex.I)))))
  exact (by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          let _object_w2 := (let _wd_1_0 := (Litex.re _value_i1 h_15);
          let _wd_1_1 := (let _wd_2_0 := (Litex.img _value_i1 h_15);
          let _wd_2_1 := (Litex.number (M := M) Complex.I);
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := (Litex.img _value_i1 h_15)
            exact (M.real_subset_complex _ (Litex.imgInR _atomic_wd_1_0))) (Litex.numberInC (M := M) Complex.I)));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.re _value_i1 h_15)
            exact (M.real_subset_complex _ (Litex.reInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.img _value_i1 h_15);
            let _wd_2_1 := (Litex.number (M := M) Complex.I);
            (Litex.mul _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := (Litex.img _value_i1 h_15)
              exact (M.real_subset_complex _ (Litex.imgInR _atomic_wd_2_0))) (Litex.numberInC (M := M) Complex.I)))
            exact (Litex.mulInC (_atomic_wd_1_0).val.left (Litex.number (M := M) Complex.I) (M.real_subset_complex _ (Litex.imgInR (_atomic_wd_1_0).val.left)) (Litex.numberInC (M := M) Complex.I)))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _value_i1 ((((Litex.NativeBridge.asComplex _value_i1 h_15)).re : ℂ) + ((((Litex.NativeBridge.asComplex _value_i1 h_15)).im : ℂ) * Complex.I)) (Litex.NativeBridge.asComplex _value_i1 h_15) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _complex := (_equal_wd_1_0).val.left; Litex.denoteRealPart _complex (Litex.NativeBridge.asComplex _value_i1 h_15) (Litex.NativeBridge.asComplex_spec _value_i1 h_15)) (Litex.NativeBridge.denoteMul ((_equal_wd_1_0).val.right).val.left (Litex.number (M := M) Complex.I) ((_equal_wd_1_0).val.right).wd.1 ((_equal_wd_1_0).val.right).wd.2 _ _ (let _complex := ((_equal_wd_1_0).val.right).val.left; Litex.denoteImaginaryPart _complex (Litex.NativeBridge.asComplex _value_i1 h_15) (Litex.NativeBridge.asComplex_spec _value_i1 h_15)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))) (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (by simpa only [add_comm, mul_comm] using (Litex.complexReconstruction (Litex.NativeBridge.asComplex _value_i1 h_15))))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_coordinate_x5f_reconstruction_x2f_statement_x2e_lit
