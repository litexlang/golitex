import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_conjugation_x5f_laws_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.C (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.conj _value_i1 h_18);
  (Litex.conj _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.conj _value_i1 h_18)
    exact (Litex.conjInC _atomic_wd_1_0))))
  let _object_w3 := (let _wd_1_0 := (Litex.conj _value_i1 h_18);
  (Litex.re _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.conj _value_i1 h_18)
    exact (Litex.conjInC _atomic_wd_1_0))))
  let _object_w4 := (Litex.re _value_i1 h_18)
  let _object_w5 := (let _wd_1_0 := (Litex.conj _value_i1 h_18);
  (Litex.img _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.conj _value_i1 h_18)
    exact (Litex.conjInC _atomic_wd_1_0))))
  let _object_w6 := (let _wd_1_0 := (Litex.img _value_i1 h_18);
  (Litex.neg _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.img _value_i1 h_18)
    exact (M.real_subset_complex _ (Litex.imgInR _atomic_wd_1_0)))))
  let _object_w7 := (let _wd_1_0 := (Litex.conj _value_i1 h_18);
  (Litex.complexAbs _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.conj _value_i1 h_18)
    exact (Litex.conjInC _atomic_wd_1_0))))
  let _object_w8 := (Litex.complexAbs _value_i1 h_18)
  exact (((by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w3
    let _equal_wd_1_1 := _object_w4
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w7
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18
          let _object_w2 := (let _wd_1_0 := (Litex.conj _value_i1 h_18);
          (Litex.conj _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.conj _value_i1 h_18)
            exact (Litex.conjInC _atomic_wd_1_0))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _value_i1 (star ((star ((Litex.NativeBridge.asComplex _value_i1 h_18))))) (Litex.NativeBridge.asComplex _value_i1 h_18) (let _complex := _equal_wd_1_0; Litex.denoteConjugate _complex (star ((Litex.NativeBridge.asComplex _value_i1 h_18))) (let _complex := (_equal_wd_1_0).val.arg; Litex.denoteConjugate _complex (Litex.NativeBridge.asComplex _value_i1 h_18) (Litex.NativeBridge.asComplex_spec _value_i1 h_18))) (Litex.NativeBridge.asComplex_spec _value_i1 h_18) (by exact star_star _))))
                )
            )
          let _object_w3 := (let _wd_1_0 := (Litex.conj _value_i1 h_18);
          (Litex.re _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.conj _value_i1 h_18)
            exact (Litex.conjInC _atomic_wd_1_0))))
          let _object_w4 := (Litex.re _value_i1 h_18)
          have h_2 : (by
            let _equal_wd_1_0 := _object_w3
            let _equal_wd_1_1 := _object_w4
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  let _equal_wd_1_1 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((star ((Litex.NativeBridge.asComplex _value_i1 h_18)))).re : ℂ) (((Litex.NativeBridge.asComplex _value_i1 h_18)).re : ℂ) (let _complex := _equal_wd_1_0; Litex.denoteRealPart _complex (star ((Litex.NativeBridge.asComplex _value_i1 h_18))) (let _complex := (_equal_wd_1_0).val.arg; Litex.denoteConjugate _complex (Litex.NativeBridge.asComplex _value_i1 h_18) (Litex.NativeBridge.asComplex_spec _value_i1 h_18))) (let _complex := _equal_wd_1_1; Litex.denoteRealPart _complex (Litex.NativeBridge.asComplex _value_i1 h_18) (Litex.NativeBridge.asComplex_spec _value_i1 h_18)) (by simp only [Complex.star_def, Complex.conj_re]))))
                )
            )
          let _object_w5 := (let _wd_1_0 := (Litex.conj _value_i1 h_18);
          (Litex.img _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.conj _value_i1 h_18)
            exact (Litex.conjInC _atomic_wd_1_0))))
          let _object_w6 := (let _wd_1_0 := (Litex.img _value_i1 h_18);
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.img _value_i1 h_18)
            exact (M.real_subset_complex _ (Litex.imgInR _atomic_wd_1_0)))))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((star ((Litex.NativeBridge.asComplex _value_i1 h_18)))).im : ℂ) (- (((Litex.NativeBridge.asComplex _value_i1 h_18)).im : ℂ)) (let _complex := _equal_wd_1_0; Litex.denoteImaginaryPart _complex (star ((Litex.NativeBridge.asComplex _value_i1 h_18))) (let _complex := (_equal_wd_1_0).val.arg; Litex.denoteConjugate _complex (Litex.NativeBridge.asComplex _value_i1 h_18) (Litex.NativeBridge.asComplex_spec _value_i1 h_18))) (Litex.NativeBridge.denoteNeg (_equal_wd_1_1).val.arg (_equal_wd_1_1).wd _ (let _complex := (_equal_wd_1_1).val.arg; Litex.denoteImaginaryPart _complex (Litex.NativeBridge.asComplex _value_i1 h_18) (Litex.NativeBridge.asComplex_spec _value_i1 h_18))) (by simp only [Complex.star_def, Complex.conj_im, Complex.ofReal_neg]))))
                )
            )
          let _object_w7 := (let _wd_1_0 := (Litex.conj _value_i1 h_18);
          (Litex.complexAbs _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.conj _value_i1 h_18)
            exact (Litex.conjInC _atomic_wd_1_0))))
          let _object_w8 := (Litex.complexAbs _value_i1 h_18)
          have h_4 : (by
            let _equal_wd_1_0 := _object_w7
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w7;
                  let _equal_wd_1_1 := _object_w8;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (‖((star ((Litex.NativeBridge.asComplex _value_i1 h_18))))‖ : ℂ) (‖((Litex.NativeBridge.asComplex _value_i1 h_18))‖ : ℂ) (let _complex := _equal_wd_1_0; Litex.denoteComplexAbs _complex (star ((Litex.NativeBridge.asComplex _value_i1 h_18))) (let _complex := (_equal_wd_1_0).val.arg; Litex.denoteConjugate _complex (Litex.NativeBridge.asComplex _value_i1 h_18) (Litex.NativeBridge.asComplex_spec _value_i1 h_18))) (let _complex := _equal_wd_1_1; Litex.denoteComplexAbs _complex (Litex.NativeBridge.asComplex _value_i1 h_18) (Litex.NativeBridge.asComplex_spec _value_i1 h_18)) (by simp only [norm_star]))))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 h_4)))
        )
      )
  )

theorem h_397 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_422 : Litex.In _value_i2 (Litex.C (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_423 : Litex.In _value_i3 (Litex.C (M := M))), (by
  let _object_w10 := (let _wd_1_0 := (Litex.add _value_i2 _value_i3 h_422 h_423);
  (Litex.conj _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC _value_i2 _value_i3 h_422 h_423))))
  let _object_w11 := (let _wd_1_0 := (Litex.conj _value_i2 h_422);
  let _wd_1_1 := (Litex.conj _value_i3 h_423);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.conj _value_i2 h_422)
    exact (Litex.conjInC _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (Litex.conj _value_i3 h_423)
    exact (Litex.conjInC _atomic_wd_1_0))))
  let _object_w12 := (let _wd_1_0 := (Litex.mul _value_i2 _value_i3 h_422 h_423);
  (Litex.conj _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC _value_i2 _value_i3 h_422 h_423))))
  let _object_w13 := (let _wd_1_0 := (Litex.conj _value_i2 h_422);
  let _wd_1_1 := (Litex.conj _value_i3 h_423);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.conj _value_i2 h_422)
    exact (Litex.conjInC _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (Litex.conj _value_i3 h_423)
    exact (Litex.conjInC _atomic_wd_1_0))))
  exact (((by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w11
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_422 _Host_i3 _rep_i3 _value_i3 h_423
          let _object_w10 := (let _wd_1_0 := (Litex.add _value_i2 _value_i3 h_422 h_423);
          (Litex.conj _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i2 _value_i3 h_422 h_423))))
          let _object_w11 := (let _wd_1_0 := (Litex.conj _value_i2 h_422);
          let _wd_1_1 := (Litex.conj _value_i3 h_423);
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.conj _value_i2 h_422)
            exact (Litex.conjInC _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.conj _value_i3 h_423)
            exact (Litex.conjInC _atomic_wd_1_0))))
          have h_395 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  let _equal_wd_1_1 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (star (((Litex.NativeBridge.asComplex _value_i2 h_422) + (Litex.NativeBridge.asComplex _value_i3 h_423)))) ((star ((Litex.NativeBridge.asComplex _value_i2 h_422))) + (star ((Litex.NativeBridge.asComplex _value_i3 h_423)))) (let _complex := _equal_wd_1_0; Litex.denoteConjugate _complex ((Litex.NativeBridge.asComplex _value_i2 h_422) + (Litex.NativeBridge.asComplex _value_i3 h_423)) (Litex.NativeBridge.denoteAdd _value_i2 _value_i3 ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 h_422) (Litex.NativeBridge.asComplex_spec _value_i3 h_423))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (let _complex := (_equal_wd_1_1).val.left; Litex.denoteConjugate _complex (Litex.NativeBridge.asComplex _value_i2 h_422) (Litex.NativeBridge.asComplex_spec _value_i2 h_422)) (let _complex := (_equal_wd_1_1).val.right; Litex.denoteConjugate _complex (Litex.NativeBridge.asComplex _value_i3 h_423) (Litex.NativeBridge.asComplex_spec _value_i3 h_423))) (by simp only [star_add]))))
                )
            )
          let _object_w12 := (let _wd_1_0 := (Litex.mul _value_i2 _value_i3 h_422 h_423);
          (Litex.conj _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInC _value_i2 _value_i3 h_422 h_423))))
          let _object_w13 := (let _wd_1_0 := (Litex.conj _value_i2 h_422);
          let _wd_1_1 := (Litex.conj _value_i3 h_423);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.conj _value_i2 h_422)
            exact (Litex.conjInC _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.conj _value_i3 h_423)
            exact (Litex.conjInC _atomic_wd_1_0))))
          have h_396 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w12;
                  let _equal_wd_1_1 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (star (((Litex.NativeBridge.asComplex _value_i2 h_422) * (Litex.NativeBridge.asComplex _value_i3 h_423)))) ((star ((Litex.NativeBridge.asComplex _value_i2 h_422))) * (star ((Litex.NativeBridge.asComplex _value_i3 h_423)))) (let _complex := _equal_wd_1_0; Litex.denoteConjugate _complex ((Litex.NativeBridge.asComplex _value_i2 h_422) * (Litex.NativeBridge.asComplex _value_i3 h_423)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 h_422) (Litex.NativeBridge.asComplex_spec _value_i3 h_423))) (Litex.NativeBridge.denoteMul (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (let _complex := (_equal_wd_1_1).val.left; Litex.denoteConjugate _complex (Litex.NativeBridge.asComplex _value_i2 h_422) (Litex.NativeBridge.asComplex_spec _value_i2 h_422)) (let _complex := (_equal_wd_1_1).val.right; Litex.denoteConjugate _complex (Litex.NativeBridge.asComplex _value_i3 h_423) (Litex.NativeBridge.asComplex_spec _value_i3 h_423))) (by simp only [star_mul, mul_comm]))))
                )
            )
          exact (And.intro h_395 h_396)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_conjugation_x5f_laws_x2f_statement_x2e_lit
