import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_parity_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_18));
  (Litex.sinh _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInR _value_i1 h_18))))
  let _object_w3 := (let _wd_1_0 := (Litex.sinh _value_i1 h_18);
  (Litex.neg _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i1 h_18)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
  let _object_w4 := (let _wd_1_0 := (_object_w2).val.arg;
  (Litex.cosh _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInR _value_i1 h_18))))
  let _object_w5 := (Litex.cosh _value_i1 h_18)
  let _object_w6 := (let _wd_1_0 := (_object_w4).val.arg;
  (Litex.tanh _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInR _value_i1 h_18))))
  let _object_w7 := (let _wd_1_0 := (Litex.tanh _value_i1 h_18);
  (Litex.neg _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.tanh _value_i1 h_18)
    exact (M.real_subset_complex _ (Litex.tanhInR _atomic_wd_1_0)))))
  let _object_w8 := (let _wd_1_0 := (_object_w6).val.arg;
  (Litex.sech _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInR _value_i1 h_18))))
  let _object_w9 := (Litex.sech _value_i1 h_18)
  exact (((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w8
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18
          let _object_w2 := (let _wd_1_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_18));
          (Litex.sinh _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInR _value_i1 h_18))))
          let _object_w3 := (let _wd_1_0 := (Litex.sinh _value_i1 h_18);
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i1 h_18)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0)))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  let _equal_wd_1_1 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.sinh ((- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)))).re : ℂ) (- (Real.sinh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteSinh _hyp ((- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))) _hyp.wd (Litex.NativeBridge.denoteNeg _value_i1 ((_equal_wd_1_0).val.arg).wd _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18))))) (Litex.NativeBridge.denoteNeg (_equal_wd_1_1).val.arg (_equal_wd_1_1).wd _ (let _hyp := (_equal_wd_1_1).val.arg; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18))))) (by simp only [Complex.neg_re, Real.sinh_neg, Complex.ofReal_neg]))))
                )
            )
          let _object_w4 := (let _wd_1_0 := (_object_w2).val.arg;
          (Litex.cosh _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInR _value_i1 h_18))))
          let _object_w5 := (Litex.cosh _value_i1 h_18)
          have h_2 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.cosh ((- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)))).re : ℂ) (Real.cosh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re : ℂ) (let _hyp := _equal_wd_1_0; Litex.denoteCosh _hyp ((- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))) _hyp.wd (Litex.NativeBridge.denoteNeg _value_i1 ((_equal_wd_1_0).val.arg).wd _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18))))) (let _hyp := _equal_wd_1_1; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18)))) (by simp only [Complex.neg_re, Real.cosh_neg]))))
                )
            )
          let _object_w6 := (let _wd_1_0 := (_object_w4).val.arg;
          (Litex.tanh _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInR _value_i1 h_18))))
          let _object_w7 := (let _wd_1_0 := (Litex.tanh _value_i1 h_18);
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.tanh _value_i1 h_18)
            exact (M.real_subset_complex _ (Litex.tanhInR _atomic_wd_1_0)))))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.tanh ((- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)))).re : ℂ) (- (Real.tanh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteTanh _hyp ((- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))) _hyp.wd (Litex.NativeBridge.denoteNeg _value_i1 ((_equal_wd_1_0).val.arg).wd _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18))))) (Litex.NativeBridge.denoteNeg (_equal_wd_1_1).val.arg (_equal_wd_1_1).wd _ (let _hyp := (_equal_wd_1_1).val.arg; Litex.denoteTanh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18))))) (by simp only [Complex.neg_re, Real.tanh_neg, Complex.ofReal_neg]))))
                )
            )
          let _object_w8 := (let _wd_1_0 := (_object_w6).val.arg;
          (Litex.sech _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInR _value_i1 h_18))))
          let _object_w9 := (Litex.sech _value_i1 h_18)
          have h_4 : (by
            let _equal_wd_1_0 := _object_w8
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w8;
                  let _equal_wd_1_1 := _object_w9;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeSech ((- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)))).re : ℂ) (Litex.nativeSech ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re : ℂ) (let _hyp := _equal_wd_1_0; Litex.denoteSech _hyp ((- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (- (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))) _hyp.wd (Litex.NativeBridge.denoteNeg _value_i1 ((_equal_wd_1_0).val.arg).wd _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18))))) (let _hyp := _equal_wd_1_1; Litex.denoteSech _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18)))) (by simp only [Complex.neg_re, Litex.nativeSech, Real.cosh_neg]))))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 h_4)))
        )
      )
  )

theorem h_796 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_809 : Litex.In _value_i2 (Litex.R (M := M))) (h_793 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w12 := (let _wd_1_0 := (Litex.neg _value_i2 (M.real_subset_complex _ h_809));
  (Litex.coth _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInR _value_i2 h_809)) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      have _premise : ¬ Litex.Same _value_i2 (Litex.number (M := M) 0) := fun h => h_793 (h.trans ((((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ))))).symm)
      have _native := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809)) _premise
      have _negated := Litex.NativeBridge.notSameOfNativeNonzero _atomic_wd_1_0 (- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))) (Litex.NativeBridge.denoteNeg _value_i2 (_atomic_wd_1_0).wd _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809))) (by simpa only [neg_ne_zero] using _native)
      exact fun h => _negated (h.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
  let _object_w13 := (let _wd_1_0 := (Litex.coth _value_i2 h_809 h_793);
  (Litex.neg _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.coth _value_i2 h_809 h_793)
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cothInRStar _atomic_wd_1_0))))))
  let _object_w14 := (let _wd_1_0 := (_object_w12).val.arg;
  (Litex.csch _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInR _value_i2 h_809)) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      have _premise : ¬ Litex.Same _value_i2 (Litex.number (M := M) 0) := fun h => h_793 (h.trans ((((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ))))).symm)
      have _native := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809)) _premise
      have _negated := Litex.NativeBridge.notSameOfNativeNonzero _atomic_wd_1_0 (- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))) (Litex.NativeBridge.denoteNeg _value_i2 (_atomic_wd_1_0).wd _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809))) (by simpa only [neg_ne_zero] using _native)
      exact fun h => _negated (h.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
  let _object_w15 := (let _wd_1_0 := (Litex.csch _value_i2 h_809 h_793);
  (Litex.neg _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.csch _value_i2 h_809 h_793)
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cschInRStar _atomic_wd_1_0))))))
  exact (((by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w14
    let _equal_wd_1_1 := _object_w15
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_809 h_793
          let _object_w12 := (let _wd_1_0 := (Litex.neg _value_i2 (M.real_subset_complex _ h_809));
          (Litex.coth _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInR _value_i2 h_809)) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              have _premise : ¬ Litex.Same _value_i2 (Litex.number (M := M) 0) := fun h => h_793 (h.trans ((((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ))))).symm)
              have _native := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809)) _premise
              have _negated := Litex.NativeBridge.notSameOfNativeNonzero _atomic_wd_1_0 (- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))) (Litex.NativeBridge.denoteNeg _value_i2 (_atomic_wd_1_0).wd _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809))) (by simpa only [neg_ne_zero] using _native)
              exact fun h => _negated (h.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
          let _object_w13 := (let _wd_1_0 := (Litex.coth _value_i2 h_809 h_793);
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.coth _value_i2 h_809 h_793)
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cothInRStar _atomic_wd_1_0))))))
          have h_794 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w12;
                  let _equal_wd_1_1 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeCoth ((- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)))).re : ℂ) (- (Litex.nativeCoth ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteCoth _hyp ((- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))) _hyp.wd.1 (Litex.NativeBridge.denoteNeg _value_i2 ((_equal_wd_1_0).val.arg).wd _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809))))) (Litex.NativeBridge.denoteNeg (_equal_wd_1_1).val.arg (_equal_wd_1_1).wd _ (let _hyp := (_equal_wd_1_1).val.arg; Litex.denoteCoth _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809))))) (by simp only [Complex.neg_re, Litex.nativeCoth, Real.cosh_neg, Real.sinh_neg, div_neg, Complex.ofReal_neg]))))
                )
            )
          let _object_w14 := (let _wd_1_0 := (_object_w12).val.arg;
          (Litex.csch _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInR _value_i2 h_809)) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              have _premise : ¬ Litex.Same _value_i2 (Litex.number (M := M) 0) := fun h => h_793 (h.trans ((((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ))))).symm)
              have _native := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809)) _premise
              have _negated := Litex.NativeBridge.notSameOfNativeNonzero _atomic_wd_1_0 (- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))) (Litex.NativeBridge.denoteNeg _value_i2 (_atomic_wd_1_0).wd _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809))) (by simpa only [neg_ne_zero] using _native)
              exact fun h => _negated (h.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
          let _object_w15 := (let _wd_1_0 := (Litex.csch _value_i2 h_809 h_793);
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.csch _value_i2 h_809 h_793)
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.cschInRStar _atomic_wd_1_0))))))
          have h_795 : (by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w14;
                  let _equal_wd_1_1 := _object_w15;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeCsch ((- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)))).re : ℂ) (- (Litex.nativeCsch ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteCsch _hyp ((- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))) _hyp.wd.1 (Litex.NativeBridge.denoteNeg _value_i2 ((_equal_wd_1_0).val.arg).wd _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809))))) (Litex.NativeBridge.denoteNeg (_equal_wd_1_1).val.arg (_equal_wd_1_1).wd _ (let _hyp := (_equal_wd_1_1).val.arg; Litex.denoteCsch _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_809)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_809))))) (by simp only [Complex.neg_re, Litex.nativeCsch, Real.sinh_neg, div_neg, Complex.ofReal_neg]))))
                )
            )
          exact (And.intro h_794 h_795)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_parity_x2f_statement_x2e_lit
