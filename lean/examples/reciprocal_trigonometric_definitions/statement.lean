import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_trigonometric_x5f_definitions_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : (by
  let _atomic_wd_1_0 := (Litex.cos _value_i1 h_19)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) (h_2 : (by
  let _atomic_wd_1_0 := (Litex.sin _value_i1 h_19)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))), (by
  let _object_w5 := (Litex.sec _value_i1 h_19 (by
    let _atomic_wd_1_0 := (Litex.cos _value_i1 h_19)
    exact h_1))
  let _object_w6 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := (Litex.cos _value_i1 h_19);
  (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (Litex.cosInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact h_1)))
  let _object_w7 := (Litex.csc _value_i1 h_19 (by
    let _atomic_wd_1_0 := (Litex.sin _value_i1 h_19)
    exact h_2))
  let _object_w8 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := (Litex.sin _value_i1 h_19);
  (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (Litex.sinInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact h_2)))
  let _object_w9 := (Litex.cot _value_i1 h_19 (by
    let _atomic_wd_1_0 := (_object_w8).val.right
    exact h_2))
  let _object_w10 := (let _wd_1_0 := (_object_w6).val.right;
  let _wd_1_1 := (_object_w8).val.right;
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (M.real_subset_complex _ (Litex.cosInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (Litex.sinInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact h_2)))
  exact (((by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w7
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w9
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 h_1 h_2
          let _object_w5 := (Litex.sec _value_i1 h_19 (by
            let _atomic_wd_1_0 := (Litex.cos _value_i1 h_19)
            exact h_1))
          let _object_w6 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.cos _value_i1 h_19);
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (Litex.cosInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_1)))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeSec ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re : ℂ) ((1 : ℂ) / (Real.cos ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteSec _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) _trig.wd.1 (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (let _trig := (Litex.cos _value_i1 h_19); Litex.denoteCos _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19))))) (by simp only [Litex.nativeSec, Complex.ofReal_div, Complex.ofReal_one]))))
                )
            )
          let _object_w7 := (Litex.csc _value_i1 h_19 (by
            let _atomic_wd_1_0 := (Litex.sin _value_i1 h_19)
            exact h_2))
          let _object_w8 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.sin _value_i1 h_19);
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (Litex.sinInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_2)))
          have h_4 : (by
            let _equal_wd_1_0 := _object_w7
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w7;
                  let _equal_wd_1_1 := _object_w8;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeCsc ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re : ℂ) ((1 : ℂ) / (Real.sin ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteCsc _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) _trig.wd.1 (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (let _trig := (Litex.sin _value_i1 h_19); Litex.denoteSin _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19))))) (by simp only [Litex.nativeCsc, Complex.ofReal_div, Complex.ofReal_one]))))
                )
            )
          let _object_w9 := (Litex.cot _value_i1 h_19 (by
            let _atomic_wd_1_0 := (_object_w8).val.right
            exact h_2))
          let _object_w10 := (let _wd_1_0 := (_object_w6).val.right;
          let _wd_1_1 := (_object_w8).val.right;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (M.real_subset_complex _ (Litex.cosInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (Litex.sinInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_2)))
          have h_5 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w9;
                  let _equal_wd_1_1 := _object_w10;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeCot ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re : ℂ) ((Real.cos ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re : ℂ) / (Real.sin ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteCot _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) _trig.wd.1 (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (let _trig := (Litex.cos _value_i1 h_19); Litex.denoteCos _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)))) (let _trig := (Litex.sin _value_i1 h_19); Litex.denoteSin _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19))))) (by simp only [Litex.nativeCot, Complex.ofReal_div]))))
                )
            )
          exact (And.intro h_3 (And.intro h_4 h_5))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_trigonometric_x5f_definitions_x2f_statement_x2e_lit
