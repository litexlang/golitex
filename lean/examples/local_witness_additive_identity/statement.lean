import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_witness_x5f_additive_x5f_identity_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v9 v10 v14 v15 v17 v18 v19 v20 v21
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_4) (Litex.numberInC (M := M) (0 : ℂ)))
  exact Litex.Same _equal_wd_1_0 _value_i1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4
          have h_18 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_19 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

          obtain ⟨_witness_i2, _member_i2⟩ := h_19

          let _value_i2 := Litex.semanticObject (M := M) _witness_i2 (M.member_isSet _member_i2)

          have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := _member_i2
          let _object_w3 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_18) (Litex.numberInC (M := M) (0 : ℂ)));
          let _wd_1_1 := _value_i2;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_18) (Litex.numberInC (M := M) (0 : ℂ)))) (M.real_subset_complex _ h_20)))

          let _object_w4 := (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_20))

          have h_3 : (by
            let _equal_wd_1_0 := _object_w3
            let _equal_wd_1_1 := _object_w4
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  let _equal_wd_1_1 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) + (0 : ℂ)) + (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_20))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) + (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_20))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_20))) (Litex.NativeBridge.denoteAdd _value_i1 _value_i2 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_20))) (by ring!))))
                )
            )

          have h_203 : Litex.Same (_object_w3).val.left _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.addCancelRightRight (_object_w3).val.left _value_i1 _value_i2 (by
                    let _atomic_wd_1_0 := (_object_w3).val.left
                    exact (Litex.addInC _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_18) (Litex.numberInC (M := M) (0 : ℂ)))) (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_20) h_3)
                )
            )
          exact h_203
        )
      )
  )

theorem h_220 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_223 : Litex.In _value_i4 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_223) (Litex.numberInC (M := M) (0 : ℂ)))
  exact Litex.Same _equal_wd_1_0 _value_i4) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_223
          have h_237 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_223
                )
            )
          have h_238 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

          obtain ⟨_witness_i5, _member_i5⟩ := h_238

          let _value_i5 := Litex.semanticObject (M := M) _witness_i5 (M.member_isSet _member_i5)

          have h_239 : Litex.In _value_i5 (Litex.R (M := M)) := _member_i5
          let _object_i6 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_239) (Litex.numberInC (M := M) (1 : ℂ)))
          have h_296 : Litex.In _object_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_239) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (Litex.addInR _value_i5 (Litex.number (M := M) (1 : ℂ)) h_239 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
                )
            )
          have h_297 : Litex.Same _object_i6 _object_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sameRefl (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_239) (Litex.numberInC (M := M) (1 : ℂ))))
                )
            )
          let _object_i7 := (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ)))
          have h_323 : Litex.Same _object_i7 (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sameRefl (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))))
                )
            )
          have h_221 : (by
            let _equal_wd_1_1 := (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ)))
            exact Litex.Same _object_i7 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_323
                )
            )
          let _object_w11 := (let _wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_237) (Litex.numberInC (M := M) (0 : ℂ)));
          let _wd_1_1 := _object_i7;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i4 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_237) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))) _wd_1_1 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _wd_1_1)).trans h_323)).symm (Litex.sameRefl (Litex.C (M := M))) (by
            let _atomic_wd_2_0 := (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ)))))))

          let _object_w12 := (Litex.add _value_i4 _object_i7 (M.real_subset_complex _ h_237) (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_323)).symm (Litex.sameRefl (Litex.C (M := M))) (by
            let _atomic_wd_2_0 := (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))))))

          have h_222 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w11;
                  let _equal_wd_1_1 := _object_w12;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_237)) + (0 : ℂ)) + (Litex.NativeBridge.asComplex _object_i7 (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_323)).symm (Litex.sameRefl (Litex.C (M := M))) (by
                    let _atomic_wd_2_0 := (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))))))) ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_237)) + (Litex.NativeBridge.asComplex _object_i7 (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_323)).symm (Litex.sameRefl (Litex.C (M := M))) (by
                    let _atomic_wd_2_0 := (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))))))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left _object_i7 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i4 (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_237)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _object_i7 (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_323)).symm (Litex.sameRefl (Litex.C (M := M))) (by
                    let _atomic_wd_2_0 := (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))))))) (Litex.NativeBridge.denoteAdd _value_i4 _object_i7 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_237)) (Litex.NativeBridge.asComplex_spec _object_i7 (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_323)).symm (Litex.sameRefl (Litex.C (M := M))) (by
                    let _atomic_wd_2_0 := (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_296) (Litex.numberInC (M := M) (1 : ℂ))))))) (by ring!))))
                )
            )
          exact (let _equal_wd_1_0 := (_object_w11).val.left;
          (show Litex.Same _equal_wd_1_0 _value_i4 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_237)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_237)) (Litex.NativeBridge.denoteAdd _value_i4 (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_237)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_237)) (by ring!))))
        )
      )
  )

theorem h_5706 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _value_i9 := Litex.semanticObject (M := M) (M.standard Litex.StandardSetValue.complex) (M.standard_isSet Litex.StandardSetValue.complex)

          have h_5710 : Litex.IsSet _value_i9 := Litex.isSet _value_i9

          let _value_i10 := Litex.semanticObject (M := M) (M.standard Litex.StandardSetValue.complex) (M.standard_isSet Litex.StandardSetValue.complex)

          have h_5711 : Litex.IsSet _value_i10 := Litex.isSet _value_i10
          have h_5707 : Litex.IsSet _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  h_5710
                )
            )
          let _object_i11 := _value_i9
          have h_5714 : Litex.Same _object_i11 _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sameRefl _value_i9)
                )
            )
          have h_5708 : Litex.Same _object_i11 _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  h_5714
                )
            )
          let _object_i12 := _value_i9
          have h_5720 : Litex.IsSet _object_i12 :=
            (by
              litex_checked_step =>
                exact (
                  h_5710
                )
            )
          have h_5721 : Litex.Same _object_i12 _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sameRefl _value_i9)
                )
            )
          have h_5709 : Litex.Same _object_i12 _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  h_5721
                )
            )
          exact (show @Eq M.Value _ _ from Eq.refl _)
        )
      )
  )

theorem h_5725 : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_5727 : Litex.In _value_i14 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.add _value_i14 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5727) (Litex.numberInC (M := M) (0 : ℂ)))
  exact Litex.Same _equal_wd_1_0 _value_i14) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_5727
          have h_5741 : Litex.In _value_i14 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5727
                )
            )
          have h_5742 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

          obtain ⟨_witness_i15, _member_i15⟩ := h_5742

          let _value_i15 := Litex.semanticObject (M := M) _witness_i15 (M.member_isSet _member_i15)

          have h_5743 : Litex.In _value_i15 (Litex.R (M := M)) := _member_i15
          let _object_w17 := (let _wd_1_0 := (Litex.add _value_i14 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5741) (Litex.numberInC (M := M) (0 : ℂ)));
          let _wd_1_1 := _value_i15;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i14 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5741) (Litex.numberInC (M := M) (0 : ℂ)))) (M.real_subset_complex _ h_5743)))

          let _object_w18 := (Litex.add _value_i14 _value_i15 (M.real_subset_complex _ h_5741) (M.real_subset_complex _ h_5743))

          have h_5726 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w17;
                  let _equal_wd_1_1 := _object_w18;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i14 (Litex.realToComplex _value_i14 h_5741)) + (0 : ℂ)) + (Litex.NativeBridge.asComplex _value_i15 (Litex.realToComplex _value_i15 h_5743))) ((Litex.NativeBridge.asComplex _value_i14 (Litex.realToComplex _value_i14 h_5741)) + (Litex.NativeBridge.asComplex _value_i15 (Litex.realToComplex _value_i15 h_5743))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left _value_i15 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i14 (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.realToComplex _value_i14 h_5741)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i15 (Litex.realToComplex _value_i15 h_5743))) (Litex.NativeBridge.denoteAdd _value_i14 _value_i15 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.realToComplex _value_i14 h_5741)) (Litex.NativeBridge.asComplex_spec _value_i15 (Litex.realToComplex _value_i15 h_5743))) (by ring!))))
                )
            )

          have h_5926 : Litex.Same (_object_w17).val.left _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.addCancelRightRight (_object_w17).val.left _value_i14 _value_i15 (by
                    let _atomic_wd_1_0 := (_object_w17).val.left
                    exact (Litex.addInC _value_i14 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5741) (Litex.numberInC (M := M) (0 : ℂ)))) (M.real_subset_complex _ h_5741) (M.real_subset_complex _ h_5743) h_5726)
                )
            )
          exact h_5926
        )
      )
  )

theorem h_5942 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_5948 : Litex.IsNonempty (Litex.N (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.natural)

          obtain ⟨_witness_i17, _member_i17⟩ := h_5948

          let _value_i17 := Litex.semanticObject (M := M) _witness_i17 (M.member_isSet _member_i17)

          have h_5949 : Litex.In _value_i17 (Litex.N (M := M)) := _member_i17

          have h_5950 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i17 h_5949)
                )
            )

          have h_5951 : Litex.IsNonempty (Litex.Z (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.integer)

          obtain ⟨_witness_i18, _member_i18⟩ := h_5951

          let _value_i18 := Litex.semanticObject (M := M) _witness_i18 (M.member_isSet _member_i18)

          have h_5952 : Litex.In _value_i18 (Litex.Z (M := M)) := _member_i18

          have h_5953 : Litex.IsNonempty (Litex.Q (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.rational)

          obtain ⟨_witness_i19, _member_i19⟩ := h_5953

          let _value_i19 := Litex.semanticObject (M := M) _witness_i19 (M.member_isSet _member_i19)

          have h_5954 : Litex.In _value_i19 (Litex.Q (M := M)) := _member_i19

          have h_5955 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

          obtain ⟨_witness_i20, _member_i20⟩ := h_5955

          let _value_i20 := Litex.semanticObject (M := M) _witness_i20 (M.member_isSet _member_i20)

          have h_5956 : Litex.In _value_i20 (Litex.R (M := M)) := _member_i20

          have h_5957 : Litex.IsNonempty (Litex.C (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.complex)

          obtain ⟨_witness_i21, _member_i21⟩ := h_5957

          let _value_i21 := Litex.semanticObject (M := M) _witness_i21 (M.member_isSet _member_i21)

          have h_5958 : Litex.In _value_i21 (Litex.C (M := M)) := _member_i21
          have h_5943 : Litex.In _value_i17 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalToComplex _value_i17 h_5949)
                )
            )
          have h_5944 : Litex.In _value_i18 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.integerToComplex _value_i18 h_5952)
                )
            )
          have h_5945 : Litex.In _value_i19 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.rationalToComplex _value_i19 h_5954)
                )
            )
          have h_5946 : Litex.In _value_i20 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (M.real_subset_complex _ h_5956)
                )
            )
          have h_5947 : Litex.In _value_i21 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5958
                )
            )
          exact (show @Eq M.Value _ _ from Eq.refl _)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_witness_x5f_additive_x5f_identity_x2f_statement_x2e_lit
