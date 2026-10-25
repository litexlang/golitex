import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_poset_x5f_maximal_x5f_element_x2f_statement_x2e_lit

universe u v1 v5 v6 v9 v12 v13 v14 v15 v16 v17 v18 v19 v20
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1)

variable (abstract_prop_2 : (Fin 2 → M.Value) → Prop)

def prop_3 (abstract_prop_2 : (Fin 2 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) : Prop :=
  ∃ (h_4 : Litex.In _value_i5 (Litex.powerSet _value_i1)), ∃ (h_6 : Litex.In _value_i6 _value_i1), ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_7 : Litex.In _value_i7 _value_i5), (abstract_prop_2 ![(Litex.denote _value_i7), (Litex.denote _value_i6)])

def prop_4 (abstract_prop_2 : (Fin 2 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) : Prop :=
  ∃ (h_11 : Litex.In _value_i9 _value_i1), ∀ (_value_i10 : Litex.Obj (M := M) M.Value) (h_12 : Litex.In _value_i10 _value_i1) (h_8 : (abstract_prop_2 ![(Litex.denote _value_i9), (Litex.denote _value_i10)])), Litex.Same _value_i10 _value_i9

theorem h_33 (abstract_prop_2 : (Fin 2 → M.Value) → Prop) {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ (h_13 : Litex.IsNonempty _value_i1) (h_15 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_52 : Litex.In _value_i12 _value_i1), (abstract_prop_2 ![(Litex.denote _value_i12), (Litex.denote _value_i12)])) (h_19 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_53 : Litex.In _value_i13 _value_i1) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_54 : Litex.In _value_i14 _value_i1) {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_55 : Litex.In _value_i15 _value_i1) (h_16 : (abstract_prop_2 ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) (h_17 : (abstract_prop_2 ![(Litex.denote _value_i14), (Litex.denote _value_i15)])), (abstract_prop_2 ![(Litex.denote _value_i13), (Litex.denote _value_i15)])) (h_23 : ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_60 : Litex.In _value_i16 _value_i1) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_61 : Litex.In _value_i17 _value_i1) (h_20 : (abstract_prop_2 ![(Litex.denote _value_i16), (Litex.denote _value_i17)])) (h_21 : (abstract_prop_2 ![(Litex.denote _value_i17), (Litex.denote _value_i16)])), Litex.Same _value_i16 _value_i17) (h_30 : ∀ {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_63 : Litex.In _value_i18 (Litex.powerSet _value_i1)) (h_27 : ∀ {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_65 : Litex.In _value_i19 _value_i18) {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_66 : Litex.In _value_i20 _value_i18), (((abstract_prop_2 ![(Litex.denote _value_i19), (Litex.denote _value_i20)])) ∨ ((abstract_prop_2 ![(Litex.denote _value_i20), (Litex.denote _value_i19)])))), ∃ (_value_i21 : Litex.Obj (M := M) M.Value), ∃ (h_67 : Litex.In _value_i21 _value_i1), ((prop_3 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) _value_i18 _value_i21)), ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_72 : Litex.In _value_i22 _value_i1), ((prop_4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) _value_i22) :=
  (by
    litex_complete =>
      exact (
        (by
          intro h_13 h_15 h_19 h_23 h_30
          have h_218 : ∃ (_value_i43 : Litex.Obj (M := M) M.Value), ∃ (h_219 : Litex.In _value_i43 _value_i1), ((prop_4 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) _value_i43) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_34 : Litex.IsNonempty _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_13
                          )
                      )
                    have h_36 : ∀ {_Host_i23 : Type _} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (h_123 : Litex.In _value_i23 _value_i1), (abstract_prop_2 ![(Litex.denote _value_i23), (Litex.denote _value_i23)]) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i23 _rep_i23 _value_i23 h_123
                              exact (h_15 _value_i23 h_123)
                            )
                          )
                      )
                    have h_40 : ∀ {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_127 : Litex.In _value_i24 _value_i1) {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (h_128 : Litex.In _value_i25 _value_i1) {_Host_i26 : Type _} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (h_129 : Litex.In _value_i26 _value_i1) (h_37 : (abstract_prop_2 ![(Litex.denote _value_i24), (Litex.denote _value_i25)])) (h_38 : (abstract_prop_2 ![(Litex.denote _value_i25), (Litex.denote _value_i26)])), (abstract_prop_2 ![(Litex.denote _value_i24), (Litex.denote _value_i26)]) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i24 _rep_i24 _value_i24 h_127 _Host_i25 _rep_i25 _value_i25 h_128 _Host_i26 _rep_i26 _value_i26 h_129 h_37 h_38
                              exact (h_19 _value_i24 h_127 _value_i25 h_128 _value_i26 h_129 h_37 h_38)
                            )
                          )
                      )
                    have h_44 : ∀ {_Host_i27 : Type _} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (h_137 : Litex.In _value_i27 _value_i1) {_Host_i28 : Type _} [_rep_i28 : Litex.Representation M _Host_i28] (_value_i28 : Litex.Obj (M := M) _Host_i28) (h_138 : Litex.In _value_i28 _value_i1) (h_41 : (abstract_prop_2 ![(Litex.denote _value_i27), (Litex.denote _value_i28)])) (h_42 : (abstract_prop_2 ![(Litex.denote _value_i28), (Litex.denote _value_i27)])), Litex.Same _value_i27 _value_i28 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i27 _rep_i27 _value_i27 h_137 _Host_i28 _rep_i28 _value_i28 h_138 h_41 h_42
                              exact (h_23 _value_i27 h_137 _value_i28 h_138 h_41 h_42)
                            )
                          )
                      )
                    have h_51 : ∀ {_Host_i29 : Type _} [_rep_i29 : Litex.Representation M _Host_i29] (_value_i29 : Litex.Obj (M := M) _Host_i29) (h_149 : Litex.In _value_i29 (Litex.powerSet _value_i1)) (h_48 : ∀ {_Host_i30 : Type _} [_rep_i30 : Litex.Representation M _Host_i30] (_value_i30 : Litex.Obj (M := M) _Host_i30) (h_151 : Litex.In _value_i30 _value_i29) {_Host_i31 : Type _} [_rep_i31 : Litex.Representation M _Host_i31] (_value_i31 : Litex.Obj (M := M) _Host_i31) (h_152 : Litex.In _value_i31 _value_i29), (((abstract_prop_2 ![(Litex.denote _value_i30), (Litex.denote _value_i31)])) ∨ ((abstract_prop_2 ![(Litex.denote _value_i31), (Litex.denote _value_i30)])))), ∃ (_value_i32 : Litex.Obj (M := M) M.Value), ∃ (h_153 : Litex.In _value_i32 _value_i1), ((prop_3 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) _value_i29 _value_i32) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i29 _rep_i29 _value_i29 h_149 h_48
                              exact (h_30 _value_i29 h_149 h_48)
                            )
                          )
                      )
                    have h_102 : Litex.IsNonempty _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_34
                          )
                      )
                    have h_104 : ∀ {_Host_i33 : Type _} [_rep_i33 : Litex.Representation M _Host_i33] (_value_i33 : Litex.Obj (M := M) _Host_i33) (h_162 : Litex.In _value_i33 _value_i1), (abstract_prop_2 ![(Litex.denote _value_i33), (Litex.denote _value_i33)]) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i33 _rep_i33 _value_i33 h_162
                              exact (h_36 _value_i33 h_162)
                            )
                          )
                      )
                    have h_108 : ∀ {_Host_i34 : Type _} [_rep_i34 : Litex.Representation M _Host_i34] (_value_i34 : Litex.Obj (M := M) _Host_i34) (h_167 : Litex.In _value_i34 _value_i1) {_Host_i35 : Type _} [_rep_i35 : Litex.Representation M _Host_i35] (_value_i35 : Litex.Obj (M := M) _Host_i35) (h_168 : Litex.In _value_i35 _value_i1) {_Host_i36 : Type _} [_rep_i36 : Litex.Representation M _Host_i36] (_value_i36 : Litex.Obj (M := M) _Host_i36) (h_169 : Litex.In _value_i36 _value_i1) (h_105 : (abstract_prop_2 ![(Litex.denote _value_i34), (Litex.denote _value_i35)])) (h_106 : (abstract_prop_2 ![(Litex.denote _value_i35), (Litex.denote _value_i36)])), (abstract_prop_2 ![(Litex.denote _value_i34), (Litex.denote _value_i36)]) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i34 _rep_i34 _value_i34 h_167 _Host_i35 _rep_i35 _value_i35 h_168 _Host_i36 _rep_i36 _value_i36 h_169 h_105 h_106
                              exact (h_40 _value_i34 h_167 _value_i35 h_168 _value_i36 h_169 h_105 h_106)
                            )
                          )
                      )
                    have h_112 : ∀ {_Host_i37 : Type _} [_rep_i37 : Litex.Representation M _Host_i37] (_value_i37 : Litex.Obj (M := M) _Host_i37) (h_184 : Litex.In _value_i37 _value_i1) {_Host_i38 : Type _} [_rep_i38 : Litex.Representation M _Host_i38] (_value_i38 : Litex.Obj (M := M) _Host_i38) (h_185 : Litex.In _value_i38 _value_i1) (h_109 : (abstract_prop_2 ![(Litex.denote _value_i37), (Litex.denote _value_i38)])) (h_110 : (abstract_prop_2 ![(Litex.denote _value_i38), (Litex.denote _value_i37)])), Litex.Same _value_i37 _value_i38 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i37 _rep_i37 _value_i37 h_184 _Host_i38 _rep_i38 _value_i38 h_185 h_109 h_110
                              exact (h_44 _value_i37 h_184 _value_i38 h_185 h_109 h_110)
                            )
                          )
                      )
                    have h_119 : ∀ {_Host_i39 : Type _} [_rep_i39 : Litex.Representation M _Host_i39] (_value_i39 : Litex.Obj (M := M) _Host_i39) (h_199 : Litex.In _value_i39 (Litex.powerSet _value_i1)) (h_116 : ∀ {_Host_i40 : Type _} [_rep_i40 : Litex.Representation M _Host_i40] (_value_i40 : Litex.Obj (M := M) _Host_i40) (h_201 : Litex.In _value_i40 _value_i39) {_Host_i41 : Type _} [_rep_i41 : Litex.Representation M _Host_i41] (_value_i41 : Litex.Obj (M := M) _Host_i41) (h_202 : Litex.In _value_i41 _value_i39), (((abstract_prop_2 ![(Litex.denote _value_i40), (Litex.denote _value_i41)])) ∨ ((abstract_prop_2 ![(Litex.denote _value_i41), (Litex.denote _value_i40)])))), ∃ (_value_i42 : Litex.Obj (M := M) M.Value), ∃ (h_203 : Litex.In _value_i42 _value_i1), ((prop_3 (M := M) abstract_prop_2 (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) _value_i39 _value_i42) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i39 _rep_i39 _value_i39 h_199 h_116
                              exact (h_51 _value_i39 h_199 h_116)
                            )
                          )
                      )
                    have _zorn_refl : ∀ x, M.mem x (Litex.denote _value_i1) → ((fun x y : M.Value => (abstract_prop_2 ![x, y])) x x) := by
                      intro x hx
                      exact h_104 (Litex.objectAtLevel x (M.member_isSet hx)) hx
                    obtain ⟨m, hm, hmax⟩ := Litex.zornMaximal _value_i1 (fun x y : M.Value => (abstract_prop_2 ![x, y])) _zorn_refl (fun x y z hx hy hz hxy hyz => h_108 (Litex.objectAtLevel x (M.member_isSet hx)) hx (Litex.objectAtLevel y (M.member_isSet hy)) hy (Litex.objectAtLevel z (M.member_isSet hz)) hz hxy hyz) (fun x y hx hy hxy hyx => h_112 (Litex.objectAtLevel x (M.member_isSet hx)) hx (Litex.objectAtLevel y (M.member_isSet hy)) hy hxy hyx) (by
                      intro c hc hchain
                      obtain ⟨b, hb, hub⟩  := h_119 (Litex.objectAtLevel (Litex.denote c) (Litex.isSet c)) hc (by
                        intro _ _ x hx _ _ y hy
                        exact hchain (Litex.denote x) (Litex.denote y) hx hy)
                      obtain ⟨_, _, hub⟩ := hub
                      refine ⟨Litex.denote b, hb, ?_⟩
                      intro x hx
                      exact hub (Litex.semanticObject x (M.member_isSet hx)) hx)
                    refine ⟨m, hm, hm, ?_⟩
                    intro x hx hmx
                    exact hmax (Litex.denote x) hx hmx
                  )
                )
            )
          exact h_218
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_poset_x5f_maximal_x5f_element_x2f_statement_x2e_lit
