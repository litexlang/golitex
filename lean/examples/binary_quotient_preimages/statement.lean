import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_binary_x5f_quotient_x5f_preimages_x2f_statement_x2e_lit

universe u v12
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (by
  intro _raw_i2 _raw_i3 h_44 h_45 h_1
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_44)
  have h_44 : Litex.In _value_i2 (Litex.R (M := M)) := h_44
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_45)
  have h_45 : Litex.In _value_i3 (Litex.R (M := M)) := h_45
  have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i3 = (M.number (0 : ℂ))))
            exact h_1)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i2 _value_i3 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45) h_1)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i2 _value_i3 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45) h_1)
    exact (Litex.divInR _value_i2 _value_i3 h_44 h_45 (_atomic_wd_1_0).wd.2.2))))
theorem h_129 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_130 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w8 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_129 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_131 : (by
  let _equal_wd_1_0 := (_object_w8 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w8 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (2 : ℂ))])) = (M.number (3 : ℂ)) from by
          have _litex_residual : (M.divValue (M.number (6 : ℂ)) (M.number (2 : ℂ))) = (M.number (3 : ℂ)) := (let _equal_wd_2_0 := (Litex.div (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((6 : ℂ) / (2 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (2 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (2 : ℂ))])) = (M.divValue (M.number (6 : ℂ)) (M.number (2 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_2 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_130 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.divValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.number (6 : ℂ)) (M.number (2 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w22 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (6 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (6 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w23 := (by
  let _preimage_builder := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_189 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => (by
  let _object_h190 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_189 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  have h_190 : Litex.In _object_h190 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_189 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  let _object_h191 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_189 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  have h_191 : Litex.In _object_h191 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_189 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  exact ∃ (h_187 : ¬ Litex.Same _object_h191 (Litex.number (M := M) (0 : ℂ))), Litex.Same (let _wd_1_0 := _object_h190;
  let _wd_1_1 := _object_h191;
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _wd_1_0 _wd_1_1 (h_129 (M := M)) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact h_190) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact h_191) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact h_187))) (Litex.number (M := M) (3 : ℂ))
)))
  exact Litex.preimage (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))

theorem h_186 : (by
  let _atomic_wd_1_0 := (_object_w22 (M := M))
  let _atomic_wd_1_1 := (_object_w23 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w22 (M := M))
          let _atomic_wd_1_1 := (_object_w23 (M := M))
          exact (by
            let _preimage := _atomic_wd_1_1
            let _preimage_builder := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_219 : Litex.In _value_i7 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => (by
            let _object_h220 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (1 : ℂ)) h_219 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            have h_220 : Litex.In _object_h220 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_219 (0 : Fin 2) (1 : ℂ) (by norm_num))
                  )
              )
            let _object_h221 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (2 : ℂ)) h_219 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            have h_221 : Litex.In _object_h221 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_219 (1 : Fin 2) (2 : ℂ) (by norm_num))
                  )
              )
            exact ∃ (h_217 : ¬ Litex.Same _object_h221 (Litex.number (M := M) (0 : ℂ))), Litex.Same (let _wd_1_0 := _object_h220;
            let _wd_1_1 := _object_h221;
            (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _wd_1_0 _wd_1_1 (h_129 (M := M)) (by
              let _atomic_wd_2_0 := _wd_1_0
              exact h_220) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact h_221) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact h_217))) (Litex.number (M := M) (3 : ℂ))
          )))
            have _preimage_same : (Litex.denote _atomic_wd_1_0) = (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.number (M := M) (6 : ℂ))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact (Litex.preimageMembers _preimage (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _atomic_wd_1_0)).mpr ⟨Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))).domain) _preimage_same) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.denote (Litex.number (M := M) (6 : ℂ))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)), (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))⟩), Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote _preimage.val.function) x = Litex.denote _preimage.val.target) _preimage_same) (h_131 (M := M))⟩))
      )
  )

theorem h_254 : (M.mem (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (2 : ℂ))]) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])) :=
  (by
    litex_complete =>
      exact (
        (by
          obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w23 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote (_object_w22 (M := M)))).mp (Litex.inOfSame (_object_w22 (M := M)) (_object_w22 (M := M)) (_object_w23 (M := M)) (_object_w23 (M := M)) (Litex.sameRefl (_object_w22 (M := M))) (show @Eq M.Value _ _ from Eq.refl _) (h_186 (M := M)))
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem (Litex.denote (_object_w22 (M := M))) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
          have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
          have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        ))
          have _preimage_repack : (Litex.denote (_object_w22 (M := M))) = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (2 : ℂ)))] := (by
          apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
          apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
          funext i
          fin_cases i <;> norm_num [Litex.FiniteFunction.index])
          exact _preimage_base)
      )
  )

theorem h_255 : (¬ ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (2 : ℂ))) = (M.number (0 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w23 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote (_object_w22 (M := M)))).mp (Litex.inOfSame (_object_w22 (M := M)) (_object_w22 (M := M)) (_object_w23 (M := M)) (_object_w23 (M := M)) (Litex.sameRefl (_object_w22 (M := M))) (show @Eq M.Value _ _ from Eq.refl _) (h_186 (M := M)))
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem (Litex.denote (_object_w22 (M := M))) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
          have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
          have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        ))
          have _preimage_repack : (Litex.denote (_object_w22 (M := M))) = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (2 : ℂ)))] := (by
          apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
          apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
          funext i
          fin_cases i <;> norm_num [Litex.FiniteFunction.index])
          exact _preimage_guard_0)
      )
  )

theorem h_256 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (2 : ℂ)))])) = (M.number (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w23 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote (_object_w22 (M := M)))).mp (Litex.inOfSame (_object_w22 (M := M)) (_object_w22 (M := M)) (_object_w23 (M := M)) (_object_w23 (M := M)) (Litex.sameRefl (_object_w22 (M := M))) (show @Eq M.Value _ _ from Eq.refl _) (h_186 (M := M)))
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem (Litex.denote (_object_w22 (M := M))) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
          have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
          have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        ))
          have _preimage_repack : (Litex.denote (_object_w22 (M := M))) = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (2 : ℂ)))] := (by
          apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
          apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
          funext i
          fin_cases i <;> norm_num [Litex.FiniteFunction.index])
          exact (Eq.mp (congrArg (fun x => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) x) = Litex.denote (Litex.number (M := M) (3 : ℂ))) _preimage_repack) _preimage_output))
      )
  )

noncomputable def _object_w38 := (let _wd_1_0 := (_object_i1 (M := M));
let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (4 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (3 : ℂ) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (4 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (3 : ℂ) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (4 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (3 : ℂ) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_267 : Litex.In _value_i9 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
))) => (by
  let _object_h268 := (Litex.cartCall _value_i9 _ (Litex.number (M := M) (1 : ℂ)) h_267 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  have h_268 : Litex.In _object_h268 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_267 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  let _object_h269 := (Litex.cartCall _value_i9 _ (Litex.number (M := M) (2 : ℂ)) h_267 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  have h_269 : Litex.In _object_h269 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_267 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  exact ∃ (h_265 : ¬ Litex.Same _object_h269 (Litex.number (M := M) (0 : ℂ))), Litex.In (let _wd_2_0 := _object_h268;
  let _wd_2_1 := _object_h269;
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _wd_1_0 _wd_2_0 _wd_2_1 (h_129 (M := M)) (by
    let _atomic_wd_1_0 := _wd_2_0
    exact h_268) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact h_269) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact h_265))) _wd_1_1
)))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))

theorem h_257 : (by
  let _atomic_wd_1_0 := (_object_w22 (M := M))
  let _atomic_wd_1_1 := (_object_w38 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w22 (M := M))
          let _atomic_wd_1_1 := (_object_w38 (M := M))
          exact (by
            let _preimage := _atomic_wd_1_1
            let _preimage_builder := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_328 : Litex.In _value_i10 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))) => (by
            let _object_h329 := (Litex.cartCall _value_i10 _ (Litex.number (M := M) (1 : ℂ)) h_328 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            have h_329 : Litex.In _object_h329 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_328 (0 : Fin 2) (1 : ℂ) (by norm_num))
                  )
              )
            let _object_h330 := (Litex.cartCall _value_i10 _ (Litex.number (M := M) (2 : ℂ)) h_328 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            have h_330 : Litex.In _object_h330 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_328 (1 : Fin 2) (2 : ℂ) (by norm_num))
                  )
              )
            exact ∃ (h_326 : ¬ Litex.Same _object_h330 (Litex.number (M := M) (0 : ℂ))), Litex.In (let _wd_1_0 := _object_h329;
            let _wd_1_1 := _object_h330;
            (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _wd_1_0 _wd_1_1 (h_129 (M := M)) (by
              let _atomic_wd_2_0 := _wd_1_0
              exact h_329) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact h_330) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact h_326))) (_atomic_wd_1_1).val.target
          )))
            have _preimage_same : (Litex.denote _atomic_wd_1_0) = (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.number (M := M) (6 : ℂ))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact (Litex.preimageSetMembers _preimage (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _atomic_wd_1_0)).mpr ⟨Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))).domain) _preimage_same) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.denote (Litex.number (M := M) (6 : ℂ))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)), (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))⟩), Eq.mpr (congrArg (fun x => M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _preimage.val.function) x) (Litex.denote _preimage.val.target)) _preimage_same) (by
            let _atomic_wd_2_0 := (_object_w8 (M := M))
            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (4 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (3 : ℂ) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (by
              let _set := _atomic_wd_2_1
              exact ((Litex.inInsert_iff _atomic_wd_2_0 _set.val.element _set.val.tail _set.wd).mpr (Or.inl (h_131 (M := M))))))⟩))
      )
  )

theorem h_408 : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (2 : ℂ)))])) (Litex.SetSemantics.insertValue (M.number (3 : ℂ)) (Litex.SetSemantics.insertValue (M.number (4 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) :=
  (by
    litex_complete =>
      exact (
        (by
          obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageSetMembers (_object_w38 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote (_object_w22 (M := M)))).mp (Litex.inOfSame (_object_w22 (M := M)) (_object_w22 (M := M)) (_object_w38 (M := M)) (_object_w38 (M := M)) (Litex.sameRefl (_object_w22 (M := M))) (show @Eq M.Value _ _ from Eq.refl _) (h_257 (M := M)))
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem (Litex.denote (_object_w22 (M := M))) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
          have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
          have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        ))
          have _preimage_repack : (Litex.denote (_object_w22 (M := M))) = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_w22 (M := M))) (M.number (2 : ℂ)))] := (by
          apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
          apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
          funext i
          fin_cases i <;> norm_num [Litex.FiniteFunction.index])
          exact (Eq.mp (congrArg (fun x => M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) x) (Litex.denote ((_object_w38 (M := M))).val.target)) _preimage_repack) _preimage_output))
      )
  )

theorem h_412 : ∀ {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_425 : Litex.In _value_i12 (_object_w23 (M := M))), (by
  have h_428 : (M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])) :=
    (by
      litex_checked_step =>
        exact (
          (by
            obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w23 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i12)).mp (Litex.inOfSame _value_i12 _value_i12 (_object_w23 (M := M)) (_object_w23 (M := M)) (Litex.sameRefl _value_i12) (show @Eq M.Value _ _ from Eq.refl _) h_425)
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
            have _preimage_guard_0 := _preimage_guard
            have _preimage_base : M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
            have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
            have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))
            have _preimage_repack : (Litex.denote _value_i12) = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ)))] := (by
            apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
            apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
            funext i
            fin_cases i <;> norm_num [Litex.FiniteFunction.index])
            exact _preimage_base)
        )
    )
  have h_409 : (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
      have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    ))
    exact Litex.In _value_i12 _atomic_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
              have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            ))
            exact h_428)
        )
    )
  let _object_h440 := (Litex.cartCall _value_i12 _ (Litex.number (M := M) (2 : ℂ)) h_409 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  exact (((by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
      have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    ))
    exact Litex.In _value_i12 _atomic_wd_1_1)) ∧ ((((by
    let _atomic_wd_1_0 := _object_h440
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) ∧ ((by
    let _equal_wd_1_0 := (by
      have _preimage_domain := ((Litex.preimageMembers (_object_w23 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i12)).mp (Litex.inOfSame _value_i12 _value_i12 (_object_w23 (M := M)) (_object_w23 (M := M)) (Litex.sameRefl _value_i12) (show @Eq M.Value _ _ from Eq.refl _) h_425)).1
      have _preimage_base : M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := by
        obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
      have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
      have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
        have _preimage_guard_0 := _preimage_guard
        have _preimage_base : M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
      have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
      have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    ))
        exact _preimage_base
      have _preimage_repack : Litex.denote _value_i12 = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ)))] := (by
      apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
      apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
      funext i
      fin_cases i <;> norm_num [Litex.FiniteFunction.index])
      exact Litex.callOn (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (_object_i1 (M := M)) (Litex.tuple (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ)))] (by
      have _finiteProof_0 := (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))
      have _finiteProof_1 := (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Eq.mp (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))).domain) _preimage_repack) _preimage_domain))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i12 _rep_i12 _value_i12 h_425
          have h_428 : (M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w23 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i12)).mp (Litex.inOfSame _value_i12 _value_i12 (_object_w23 (M := M)) (_object_w23 (M := M)) (Litex.sameRefl _value_i12) (show @Eq M.Value _ _ from Eq.refl _) h_425)
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
                    have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
                    have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    have _preimage_guard_0 := _preimage_guard
                    have _preimage_base : M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                    have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                    have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))
                    have _preimage_repack : (Litex.denote _value_i12) = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ)))] := (by
                    apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                    apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                    funext i
                    fin_cases i <;> norm_num [Litex.FiniteFunction.index])
                    exact _preimage_base)
                )
            )
          have h_429 : (¬ ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ))) = (M.number (0 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w23 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i12)).mp (Litex.inOfSame _value_i12 _value_i12 (_object_w23 (M := M)) (_object_w23 (M := M)) (Litex.sameRefl _value_i12) (show @Eq M.Value _ _ from Eq.refl _) h_425)
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
                    have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
                    have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    have _preimage_guard_0 := _preimage_guard
                    have _preimage_base : M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                    have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                    have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))
                    have _preimage_repack : (Litex.denote _value_i12) = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ)))] := (by
                    apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                    apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                    funext i
                    fin_cases i <;> norm_num [Litex.FiniteFunction.index])
                    exact _preimage_guard_0)
                )
            )
          have h_430 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ)))])) = (M.number (3 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.preimageMembers (_object_w23 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i12)).mp (Litex.inOfSame _value_i12 _value_i12 (_object_w23 (M := M)) (_object_w23 (M := M)) (Litex.sameRefl _value_i12) (show @Eq M.Value _ _ from Eq.refl _) h_425)
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
                    have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
                    have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    have _preimage_guard_0 := _preimage_guard
                    have _preimage_base : M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                    have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                    have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))
                    have _preimage_repack : (Litex.denote _value_i12) = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ)))] := (by
                    apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                    apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                    funext i
                    fin_cases i <;> norm_num [Litex.FiniteFunction.index])
                    exact (Eq.mp (congrArg (fun x => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) x) = Litex.denote (Litex.number (M := M) (3 : ℂ))) _preimage_repack) _preimage_output))
                )
            )
          have h_409 : (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
              have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            ))
            exact Litex.In _value_i12 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
                      have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))
                    exact h_428)
                )
            )
          let _object_h439 := (Litex.cartCall _value_i12 _ (Litex.number (M := M) (1 : ℂ)) h_409 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_439 : Litex.In _object_h439 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_409 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h440 := (Litex.cartCall _value_i12 _ (Litex.number (M := M) (2 : ℂ)) h_409 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_440 : Litex.In _object_h440 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_409 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_410 : (by
            let _atomic_wd_1_0 := _object_h440
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_h440
                    exact h_429)
                )
            )
          have h_411 : (by
            let _equal_wd_1_0 := (by
              have _preimage_domain := ((Litex.preimageMembers (_object_w23 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i12)).mp (Litex.inOfSame _value_i12 _value_i12 (_object_w23 (M := M)) (_object_w23 (M := M)) (Litex.sameRefl _value_i12) (show @Eq M.Value _ _ from Eq.refl _) h_425)).1
              have _preimage_base : M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := by
                obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
              have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
              have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                have _preimage_guard_0 := _preimage_guard
                have _preimage_base : M.mem (Litex.denote _value_i12) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
              have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
              have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            ))
                exact _preimage_base
              have _preimage_repack : Litex.denote _value_i12 = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ)))] := (by
              apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
              apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
              funext i
              fin_cases i <;> norm_num [Litex.FiniteFunction.index])
              exact Litex.callOn (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (_object_i1 (M := M)) (Litex.tuple (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i12) (M.number (2 : ℂ)))] (by
              have _finiteProof_0 := (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))
              have _finiteProof_1 := (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Eq.mp (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))).domain) _preimage_repack) _preimage_domain))
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  h_430
                )
            )
          exact (And.intro h_409 (And.intro h_410 h_411))
        )
      )
  )

theorem h_446 : (by
  let _atomic_wd_1_0 := (_object_w38 (M := M))
  let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  ))
  exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w38 (M := M))
          let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))
          exact (by
            let _preimage := _atomic_wd_1_0
            let _preimage_builder := (Litex.setBuilder _atomic_wd_1_1 (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_449 : Litex.In _value_i14 _atomic_wd_1_1) => (by
            let _object_h450 := (Litex.cartCall _value_i14 _ (Litex.number (M := M) (1 : ℂ)) h_449 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            have h_450 : Litex.In _object_h450 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_449 (0 : Fin 2) (1 : ℂ) (by norm_num))
                  )
              )
            let _object_h451 := (Litex.cartCall _value_i14 _ (Litex.number (M := M) (2 : ℂ)) h_449 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            have h_451 : Litex.In _object_h451 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_449 (1 : Fin 2) (2 : ℂ) (by norm_num))
                  )
              )
            exact ∃ (h_447 : ¬ Litex.Same _object_h451 (Litex.number (M := M) (0 : ℂ))), Litex.In (let _wd_1_0 := _object_h450;
            let _wd_1_1 := _object_h451;
            (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _wd_1_0 _wd_1_1 (h_129 (M := M)) (by
              let _atomic_wd_2_0 := _wd_1_0
              exact h_450) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact h_451) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact h_447))) ((_object_w38 (M := M))).val.target
          )))
            change Litex.Subset _preimage _atomic_wd_1_1
            intro _preimage_input _preimage_member
            have _preimage_domain := ((Litex.preimageSetMembers _preimage (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) ((h_130 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) _preimage_input).mp _preimage_member).1
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
            have _preimage_guard_0 := _preimage_guard
            have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
            have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
            have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))
            exact Eq.mp (congrArg (M.mem _preimage_input) (Litex.sameRefl _atomic_wd_1_1)) _preimage_base))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_binary_x5f_quotient_x5f_preimages_x2f_statement_x2e_lit
