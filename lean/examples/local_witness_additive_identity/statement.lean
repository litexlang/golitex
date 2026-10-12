import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_witness_x5f_additive_x5f_identity_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v9 v10 v14 v15 v17 v18 v19 v20 v21
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_4) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_4
    have h_18 : Litex.In _value_i1 (Litex.R (M := M)) :=
      h_4
    have h_19 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)
    
    obtain ⟨_witness_i2, _member_i2⟩ := h_19
    
    let _value_i2 := Litex.semanticObject (M := M) _witness_i2 (M.member_isSet _member_i2)
    
    have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := _member_i2
    have h_3 : Litex.Same (Litex.add (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))) _value_i2 (Litex.addInC _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.realToComplex _value_i2 h_20)) (Litex.add _value_i1 _value_i2 (Litex.realToComplex _value_i1 h_18) (Litex.realToComplex _value_i2 h_20)) :=
      (Litex.NativeBridge.sameOfDenoteNumber (Litex.add (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))) _value_i2 (Litex.addInC _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.realToComplex _value_i2 h_20)) (Litex.add _value_i1 _value_i2 (Litex.realToComplex _value_i1 h_18) (Litex.realToComplex _value_i2 h_20)) (((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) + (0 : ℂ)) + (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_20))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) + (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_20))) (Litex.NativeBridge.denoteAdd (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))) _value_i2 (Litex.addInC _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.realToComplex _value_i2 h_20) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_20)) (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) (0 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_20))) (Litex.NativeBridge.denoteAdd _value_i1 _value_i2 (Litex.realToComplex _value_i1 h_18) (Litex.realToComplex _value_i2 h_20) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_20)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_20))) (by ring))
    
    have h_203 : Litex.Same (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 :=
      (Litex.addCancelRightRight (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 _value_i2 (Litex.addInC _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.realToComplex _value_i1 h_18) (Litex.realToComplex _value_i2 h_20) h_3)
    exact (((Litex.sameRefl (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_18) (Litex.numberInC (M := M) (0 : ℂ))))).trans h_203)
  )

theorem h_238 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_241 : Litex.In _value_i4 (Litex.R (M := M))), Litex.Same (Litex.add _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_241) (Litex.numberInC (M := M) (0 : ℂ))) _value_i4 :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 h_241
    have h_255 : Litex.In _value_i4 (Litex.R (M := M)) :=
      h_241
    have h_256 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)
    
    obtain ⟨_witness_i5, _member_i5⟩ := h_256
    
    let _value_i5 := Litex.semanticObject (M := M) _witness_i5 (M.member_isSet _member_i5)
    
    have h_257 : Litex.In _value_i5 (Litex.R (M := M)) := _member_i5
    let _object_i6 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i5 h_257) (Litex.numberInC (M := M) (1 : ℂ)))
    have h_314 : Litex.In _object_i6 (Litex.R (M := M)) :=
      (Litex.addInR _value_i5 (Litex.number (M := M) (1 : ℂ)) h_257 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))))
    have h_315 : Litex.Same _object_i6 (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i5 h_257) (Litex.numberInC (M := M) (1 : ℂ))) :=
      (Litex.sameRefl (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i5 h_257) (Litex.numberInC (M := M) (1 : ℂ))))
    let _object_i7 := (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ)))
    have h_341 : Litex.Same _object_i7 (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))) :=
      (Litex.sameRefl (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))))
    have h_239 : Litex.Same _object_i7 (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))) :=
      (((Litex.sameRefl _object_i7)).trans h_341)
    have h_240 : Litex.Same (Litex.add (Litex.add _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_255) (Litex.numberInC (M := M) (0 : ℂ))) _object_i7 (Litex.addInC _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_255) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_341)).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))))) (Litex.add _value_i4 _object_i7 (Litex.realToComplex _value_i4 h_255) (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_341)).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))))) :=
      (Litex.NativeBridge.sameOfDenoteNumber (Litex.add (Litex.add _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_255) (Litex.numberInC (M := M) (0 : ℂ))) _object_i7 (Litex.addInC _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_255) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_341)).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))))) (Litex.add _value_i4 _object_i7 (Litex.realToComplex _value_i4 h_255) (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_341)).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))))) (((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_255)) + (0 : ℂ)) + (((Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_257)) + (1 : ℂ)) + (1 : ℂ))) ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_255)) + (((Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_257)) + (1 : ℂ)) + (1 : ℂ))) (Litex.NativeBridge.denoteAdd (Litex.add _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_255) (Litex.numberInC (M := M) (0 : ℂ))) _object_i7 (Litex.addInC _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_255) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_341)).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ)))) ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_255)) + (0 : ℂ)) (((Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_257)) + (1 : ℂ)) + (1 : ℂ)) (Litex.NativeBridge.denoteAdd _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_255) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_255)) (0 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_255)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteAdd _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ)) ((Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_257)) + (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteAdd _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i5 h_257) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_257)) (1 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.realToComplex _value_i5 h_257)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteAdd _value_i4 _object_i7 (Litex.realToComplex _value_i4 h_255) (Litex.inOfSame (Litex.add _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ))) _object_i7 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i7)).trans h_341)).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.addInC _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_255)) (((Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_257)) + (1 : ℂ)) + (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_255)) (Litex.NativeBridge.denoteAdd _object_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_i6 h_314) (Litex.numberInC (M := M) (1 : ℂ)) ((Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_257)) + (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteAdd _value_i5 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i5 h_257) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_257)) (1 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.realToComplex _value_i5 h_257)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by ring))
    exact (Litex.NativeBridge.sameOfDenoteNumber (Litex.add _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_255) (Litex.numberInC (M := M) (0 : ℂ))) _value_i4 ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_255)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_255)) (Litex.NativeBridge.denoteAdd _value_i4 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i4 h_255) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_255)) (0 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_255)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_255)) (by ring))
  )

theorem h_5724 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    let _value_i9 := Litex.semanticObject (M := M) (M.standard Litex.StandardSetValue.complex) (M.standard_isSet Litex.StandardSetValue.complex)
    
    have h_5728 : Litex.IsSet _value_i9 := Litex.isSet _value_i9
    
    let _value_i10 := Litex.semanticObject (M := M) (M.standard Litex.StandardSetValue.complex) (M.standard_isSet Litex.StandardSetValue.complex)
    
    have h_5729 : Litex.IsSet _value_i10 := Litex.isSet _value_i10
    have h_5725 : Litex.IsSet _value_i9 :=
      h_5728
    let _object_i11 := _value_i9
    have h_5732 : Litex.Same _object_i11 _value_i9 :=
      (Litex.sameRefl _value_i9)
    have h_5726 : Litex.Same _object_i11 _value_i9 :=
      (((Litex.sameRefl _object_i11)).trans h_5732)
    let _object_i12 := _value_i9
    have h_5738 : Litex.IsSet _object_i12 :=
      h_5728
    have h_5739 : Litex.Same _object_i12 _value_i9 :=
      (Litex.sameRefl _value_i9)
    have h_5727 : Litex.Same _object_i12 _value_i9 :=
      (((Litex.sameRefl _object_i12)).trans h_5739)
    exact (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))
  )

theorem h_5743 : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_5745 : Litex.In _value_i14 (Litex.R (M := M))), Litex.Same (Litex.add _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5745) (Litex.numberInC (M := M) (0 : ℂ))) _value_i14 :=
  (by
    intro _Host_i14 _rep_i14 _value_i14 h_5745
    have h_5759 : Litex.In _value_i14 (Litex.R (M := M)) :=
      h_5745
    have h_5760 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)
    
    obtain ⟨_witness_i15, _member_i15⟩ := h_5760
    
    let _value_i15 := Litex.semanticObject (M := M) _witness_i15 (M.member_isSet _member_i15)
    
    have h_5761 : Litex.In _value_i15 (Litex.R (M := M)) := _member_i15
    have h_5744 : Litex.Same (Litex.add (Litex.add _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))) _value_i15 (Litex.addInC _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.realToComplex _value_i15 h_5761)) (Litex.add _value_i14 _value_i15 (Litex.realToComplex _value_i14 h_5759) (Litex.realToComplex _value_i15 h_5761)) :=
      (Litex.NativeBridge.sameOfDenoteNumber (Litex.add (Litex.add _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))) _value_i15 (Litex.addInC _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.realToComplex _value_i15 h_5761)) (Litex.add _value_i14 _value_i15 (Litex.realToComplex _value_i14 h_5759) (Litex.realToComplex _value_i15 h_5761)) (((Litex.NativeBridge.asComplex _value_i14 (Litex.realToComplex _value_i14 h_5759)) + (0 : ℂ)) + (Litex.NativeBridge.asComplex _value_i15 (Litex.realToComplex _value_i15 h_5761))) ((Litex.NativeBridge.asComplex _value_i14 (Litex.realToComplex _value_i14 h_5759)) + (Litex.NativeBridge.asComplex _value_i15 (Litex.realToComplex _value_i15 h_5761))) (Litex.NativeBridge.denoteAdd (Litex.add _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))) _value_i15 (Litex.addInC _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.realToComplex _value_i15 h_5761) ((Litex.NativeBridge.asComplex _value_i14 (Litex.realToComplex _value_i14 h_5759)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i15 (Litex.realToComplex _value_i15 h_5761)) (Litex.NativeBridge.denoteAdd _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i14 (Litex.realToComplex _value_i14 h_5759)) (0 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.realToComplex _value_i14 h_5759)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i15 (Litex.realToComplex _value_i15 h_5761))) (Litex.NativeBridge.denoteAdd _value_i14 _value_i15 (Litex.realToComplex _value_i14 h_5759) (Litex.realToComplex _value_i15 h_5761) (Litex.NativeBridge.asComplex _value_i14 (Litex.realToComplex _value_i14 h_5759)) (Litex.NativeBridge.asComplex _value_i15 (Litex.realToComplex _value_i15 h_5761)) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.realToComplex _value_i14 h_5759)) (Litex.NativeBridge.asComplex_spec _value_i15 (Litex.realToComplex _value_i15 h_5761))) (by ring))
    
    have h_5944 : Litex.Same (Litex.add _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))) _value_i14 :=
      (Litex.addCancelRightRight (Litex.add _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))) _value_i14 _value_i15 (Litex.addInC _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.realToComplex _value_i14 h_5759) (Litex.realToComplex _value_i15 h_5761) h_5744)
    exact (((Litex.sameRefl (Litex.add _value_i14 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i14 h_5759) (Litex.numberInC (M := M) (0 : ℂ))))).trans h_5944)
  )

theorem h_5978 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    have h_5984 : Litex.IsNonempty (Litex.N (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.natural)
    
    obtain ⟨_witness_i17, _member_i17⟩ := h_5984
    
    let _value_i17 := Litex.semanticObject (M := M) _witness_i17 (M.member_isSet _member_i17)
    
    have h_5985 : Litex.In _value_i17 (Litex.N (M := M)) := _member_i17
    
    have h_5986 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
      (Litex.naturalNonnegative _value_i17 h_5985)
    
    have h_6003 : Litex.IsNonempty (Litex.Z (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.integer)
    
    obtain ⟨_witness_i18, _member_i18⟩ := h_6003
    
    let _value_i18 := Litex.semanticObject (M := M) _witness_i18 (M.member_isSet _member_i18)
    
    have h_6004 : Litex.In _value_i18 (Litex.Z (M := M)) := _member_i18
    
    have h_6005 : Litex.IsNonempty (Litex.Q (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.rational)
    
    obtain ⟨_witness_i19, _member_i19⟩ := h_6005
    
    let _value_i19 := Litex.semanticObject (M := M) _witness_i19 (M.member_isSet _member_i19)
    
    have h_6006 : Litex.In _value_i19 (Litex.Q (M := M)) := _member_i19
    
    have h_6007 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)
    
    obtain ⟨_witness_i20, _member_i20⟩ := h_6007
    
    let _value_i20 := Litex.semanticObject (M := M) _witness_i20 (M.member_isSet _member_i20)
    
    have h_6008 : Litex.In _value_i20 (Litex.R (M := M)) := _member_i20
    
    have h_6009 : Litex.IsNonempty (Litex.C (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.complex)
    
    obtain ⟨_witness_i21, _member_i21⟩ := h_6009
    
    let _value_i21 := Litex.semanticObject (M := M) _witness_i21 (M.member_isSet _member_i21)
    
    have h_6010 : Litex.In _value_i21 (Litex.C (M := M)) := _member_i21
    have h_5979 : Litex.In _value_i17 (Litex.C (M := M)) :=
      (Litex.naturalToComplex _value_i17 h_5985)
    have h_5980 : Litex.In _value_i18 (Litex.C (M := M)) :=
      (Litex.integerToComplex _value_i18 h_6004)
    have h_5981 : Litex.In _value_i19 (Litex.C (M := M)) :=
      (Litex.rationalToComplex _value_i19 h_6006)
    have h_5982 : Litex.In _value_i20 (Litex.C (M := M)) :=
      (Litex.realToComplex _value_i20 h_6008)
    have h_5983 : Litex.In _value_i21 (Litex.C (M := M)) :=
      h_6010
    exact (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))
  )
end LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_witness_x5f_additive_x5f_identity_x2f_statement_x2e_lit
