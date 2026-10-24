import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_line_x5f_witnesses_x2f_statement_x2e_lit

universe u v1 v14
variable {M : Litex.Semantics.{u}}

theorem h_25 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_38 : Litex.In _value_i1 (Litex.R (M := M))), ((∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_39 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 _value_i1) ∧ (((∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_45 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same _value_i1 _value_i3) ∧ (((∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_51 : Litex.In _value_i4 (Litex.R (M := M))), ¬ Litex.Same _value_i4 _value_i1) ∧ (((∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_57 : Litex.In _value_i5 (Litex.R (M := M))), ¬ Litex.Same _value_i1 _value_i5) ∧ (((∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_63 : Litex.In _value_i6 (Litex.R (M := M))), Litex.Lt _value_i6 _value_i1) ∧ (((∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_92 : Litex.In _value_i7 (Litex.R (M := M))), Litex.Lt _value_i1 _value_i7) ∧ (((∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_123 : Litex.In _value_i8 (Litex.R (M := M))), Litex.Lt _value_i1 _value_i8) ∧ (((∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_154 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Lt _value_i9 _value_i1) ∧ (((∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_183 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Le _value_i10 _value_i1) ∧ (((∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_241 : Litex.In _value_i11 (Litex.R (M := M))), Litex.Le _value_i1 _value_i11) ∧ (((∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_299 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Le _value_i1 _value_i12) ∧ (∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (h_357 : Litex.In _value_i13 (Litex.R (M := M))), Litex.Le _value_i13 _value_i1)))))))))))))))))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_38
          have h_2 : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_39 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  ⟨Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1), h_38, (by rfl)⟩
                )
            )
          have h_4 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_45 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same _value_i1 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  ⟨Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1), h_38, (by rfl)⟩
                )
            )
          have h_6 : ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_51 : Litex.In _value_i4 (Litex.R (M := M))), ¬ Litex.Same _value_i4 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, (Litex.ltNotSame _real_witness _real_base _real_order)⟩)
                )
            )
          have h_8 : ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_57 : Litex.In _value_i5 (Litex.R (M := M))), ¬ Litex.Same _value_i1 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, (Litex.ltNotSame _real_base _real_witness _real_order)⟩)
                )
            )
          have h_10 : ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_63 : Litex.In _value_i6 (Litex.R (M := M))), Litex.Lt _value_i6 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, _real_order⟩)
                )
            )
          have h_12 : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_92 : Litex.In _value_i7 (Litex.R (M := M))), Litex.Lt _value_i1 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, _real_order⟩)
                )
            )
          have h_14 : ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_123 : Litex.In _value_i8 (Litex.R (M := M))), Litex.Lt _value_i1 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, _real_order⟩)
                )
            )
          have h_16 : ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_154 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Lt _value_i9 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, _real_order⟩)
                )
            )
          have h_18 : ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_183 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Le _value_i10 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, (Litex.ltToLe _real_witness _real_base _real_order)⟩)
                )
            )
          have h_20 : ∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_241 : Litex.In _value_i11 (Litex.R (M := M))), Litex.Le _value_i1 _value_i11 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, (Litex.ltToLe _real_base _real_witness _real_order)⟩)
                )
            )
          have h_22 : ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_299 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Le _value_i1 _value_i12 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, (Litex.ltToLe _real_base _real_witness _real_order)⟩)
                )
            )
          have h_24 : ∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (h_357 : Litex.In _value_i13 (Litex.R (M := M))), Litex.Le _value_i13 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := _value_i1
                    have _real_base_member : Litex.In _real_base Litex.R := h_38
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, (Litex.ltToLe _real_witness _real_base _real_order)⟩)
                )
            )
          exact (And.intro h_2 (And.intro h_4 (And.intro h_6 (And.intro h_8 (And.intro h_10 (And.intro h_12 (And.intro h_14 (And.intro h_16 (And.intro h_18 (And.intro h_20 (And.intro h_22 h_24)))))))))))
        )
      )
  )

theorem h_439 : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_454 : Litex.In _value_i14 (Litex.R (M := M))), ((∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (h_455 : Litex.In _value_i15 (Litex.R (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_456 : Litex.In _value_i16 (Litex.R (M := M))), Litex.Same _value_i15 _value_i16) ∧ (((∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_457 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_458 : Litex.In _value_i18 (Litex.R (M := M))), Litex.Same _value_i18 _value_i17) ∧ (((∃ (_value_i19 : Litex.Obj (M := M) M.Value), ∃ (h_459 : Litex.In _value_i19 (Litex.R (M := M))), ∃ (_value_i20 : Litex.Obj (M := M) M.Value), ∃ (h_460 : Litex.In _value_i20 (Litex.R (M := M))), ¬ Litex.Same _value_i19 _value_i20) ∧ (((∃ (_value_i21 : Litex.Obj (M := M) M.Value), ∃ (h_461 : Litex.In _value_i21 (Litex.R (M := M))), ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_462 : Litex.In _value_i22 (Litex.R (M := M))), ¬ Litex.Same _value_i22 _value_i21) ∧ (((∃ (_value_i23 : Litex.Obj (M := M) M.Value), ∃ (h_463 : Litex.In _value_i23 (Litex.R (M := M))), ∃ (_value_i24 : Litex.Obj (M := M) M.Value), ∃ (h_464 : Litex.In _value_i24 (Litex.R (M := M))), Litex.Lt _value_i23 _value_i24) ∧ (((∃ (_value_i25 : Litex.Obj (M := M) M.Value), ∃ (h_490 : Litex.In _value_i25 (Litex.R (M := M))), ∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (h_491 : Litex.In _value_i26 (Litex.R (M := M))), Litex.Lt _value_i26 _value_i25) ∧ (((∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (h_519 : Litex.In _value_i27 (Litex.R (M := M))), ∃ (_value_i28 : Litex.Obj (M := M) M.Value), ∃ (h_520 : Litex.In _value_i28 (Litex.R (M := M))), Litex.Lt _value_i28 _value_i27) ∧ (((∃ (_value_i29 : Litex.Obj (M := M) M.Value), ∃ (h_548 : Litex.In _value_i29 (Litex.R (M := M))), ∃ (_value_i30 : Litex.Obj (M := M) M.Value), ∃ (h_549 : Litex.In _value_i30 (Litex.R (M := M))), Litex.Lt _value_i29 _value_i30) ∧ (((∃ (_value_i31 : Litex.Obj (M := M) M.Value), ∃ (h_575 : Litex.In _value_i31 (Litex.R (M := M))), ∃ (_value_i32 : Litex.Obj (M := M) M.Value), ∃ (h_576 : Litex.In _value_i32 (Litex.R (M := M))), Litex.Le _value_i31 _value_i32) ∧ (((∃ (_value_i33 : Litex.Obj (M := M) M.Value), ∃ (h_639 : Litex.In _value_i33 (Litex.R (M := M))), ∃ (_value_i34 : Litex.Obj (M := M) M.Value), ∃ (h_640 : Litex.In _value_i34 (Litex.R (M := M))), Litex.Le _value_i34 _value_i33) ∧ (((∃ (_value_i35 : Litex.Obj (M := M) M.Value), ∃ (h_703 : Litex.In _value_i35 (Litex.R (M := M))), ∃ (_value_i36 : Litex.Obj (M := M) M.Value), ∃ (h_704 : Litex.In _value_i36 (Litex.R (M := M))), Litex.Le _value_i36 _value_i35) ∧ (∃ (_value_i37 : Litex.Obj (M := M) M.Value), ∃ (h_767 : Litex.In _value_i37 (Litex.R (M := M))), ∃ (_value_i38 : Litex.Obj (M := M) M.Value), ∃ (h_768 : Litex.In _value_i38 (Litex.R (M := M))), Litex.Le _value_i37 _value_i38)))))))))))))))))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_454
          have h_416 : ∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (h_455 : Litex.In _value_i15 (Litex.R (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_456 : Litex.In _value_i16 (Litex.R (M := M))), Litex.Same _value_i15 _value_i16 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    exact ⟨_real_base, _real_base_member, _real_base, _real_base_member, (by rfl)⟩)
                )
            )
          have h_418 : ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_457 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_458 : Litex.In _value_i18 (Litex.R (M := M))), Litex.Same _value_i18 _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    exact ⟨_real_base, _real_base_member, _real_base, _real_base_member, (by rfl)⟩)
                )
            )
          have h_420 : ∃ (_value_i19 : Litex.Obj (M := M) M.Value), ∃ (h_459 : Litex.In _value_i19 (Litex.R (M := M))), ∃ (_value_i20 : Litex.Obj (M := M) M.Value), ∃ (h_460 : Litex.In _value_i20 (Litex.R (M := M))), ¬ Litex.Same _value_i19 _value_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, (Litex.ltNotSame _real_base _real_witness _real_order)⟩)
                )
            )
          have h_422 : ∃ (_value_i21 : Litex.Obj (M := M) M.Value), ∃ (h_461 : Litex.In _value_i21 (Litex.R (M := M))), ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_462 : Litex.In _value_i22 (Litex.R (M := M))), ¬ Litex.Same _value_i22 _value_i21 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, (Litex.ltNotSame _real_witness _real_base _real_order)⟩)
                )
            )
          have h_424 : ∃ (_value_i23 : Litex.Obj (M := M) M.Value), ∃ (h_463 : Litex.In _value_i23 (Litex.R (M := M))), ∃ (_value_i24 : Litex.Obj (M := M) M.Value), ∃ (h_464 : Litex.In _value_i24 (Litex.R (M := M))), Litex.Lt _value_i23 _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, _real_order⟩)
                )
            )
          have h_426 : ∃ (_value_i25 : Litex.Obj (M := M) M.Value), ∃ (h_490 : Litex.In _value_i25 (Litex.R (M := M))), ∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (h_491 : Litex.In _value_i26 (Litex.R (M := M))), Litex.Lt _value_i26 _value_i25 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, _real_order⟩)
                )
            )
          have h_428 : ∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (h_519 : Litex.In _value_i27 (Litex.R (M := M))), ∃ (_value_i28 : Litex.Obj (M := M) M.Value), ∃ (h_520 : Litex.In _value_i28 (Litex.R (M := M))), Litex.Lt _value_i28 _value_i27 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, _real_order⟩)
                )
            )
          have h_430 : ∃ (_value_i29 : Litex.Obj (M := M) M.Value), ∃ (h_548 : Litex.In _value_i29 (Litex.R (M := M))), ∃ (_value_i30 : Litex.Obj (M := M) M.Value), ∃ (h_549 : Litex.In _value_i30 (Litex.R (M := M))), Litex.Lt _value_i29 _value_i30 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, _real_order⟩)
                )
            )
          have h_432 : ∃ (_value_i31 : Litex.Obj (M := M) M.Value), ∃ (h_575 : Litex.In _value_i31 (Litex.R (M := M))), ∃ (_value_i32 : Litex.Obj (M := M) M.Value), ∃ (h_576 : Litex.In _value_i32 (Litex.R (M := M))), Litex.Le _value_i31 _value_i32 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, (Litex.ltToLe _real_base _real_witness _real_order)⟩)
                )
            )
          have h_434 : ∃ (_value_i33 : Litex.Obj (M := M) M.Value), ∃ (h_639 : Litex.In _value_i33 (Litex.R (M := M))), ∃ (_value_i34 : Litex.Obj (M := M) M.Value), ∃ (h_640 : Litex.In _value_i34 (Litex.R (M := M))), Litex.Le _value_i34 _value_i33 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, (Litex.ltToLe _real_witness _real_base _real_order)⟩)
                )
            )
          have h_436 : ∃ (_value_i35 : Litex.Obj (M := M) M.Value), ∃ (h_703 : Litex.In _value_i35 (Litex.R (M := M))), ∃ (_value_i36 : Litex.Obj (M := M) M.Value), ∃ (h_704 : Litex.In _value_i36 (Litex.R (M := M))), Litex.Le _value_i36 _value_i35 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, (Litex.ltToLe _real_witness _real_base _real_order)⟩)
                )
            )
          have h_438 : ∃ (_value_i37 : Litex.Obj (M := M) M.Value), ∃ (h_767 : Litex.In _value_i37 (Litex.R (M := M))), ∃ (_value_i38 : Litex.Obj (M := M) M.Value), ∃ (h_768 : Litex.In _value_i38 (Litex.R (M := M))), Litex.Le _value_i37 _value_i38 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
                    have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
                    exact ⟨_real_base, _real_base_member, _real_witness, _real_member, (Litex.ltToLe _real_base _real_witness _real_order)⟩)
                )
            )
          exact (And.intro h_416 (And.intro h_418 (And.intro h_420 (And.intro h_422 (And.intro h_424 (And.intro h_426 (And.intro h_428 (And.intro h_430 (And.intro h_432 (And.intro h_434 (And.intro h_436 h_438)))))))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_line_x5f_witnesses_x2f_statement_x2e_lit
