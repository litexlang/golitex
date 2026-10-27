import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_zero_x5f_matrix_x5f_definition_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.N (M := M))), (by
  let _object_w18 := (Litex.zeroMatrix _value_i1 _value_i2 h_15 h_17)
  let _object_w19 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.number (0 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
    have _litex_checked_return : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))) → M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17))) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → M.mem ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.number (0 : ℂ))) _raw_i3 _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
      intro _raw_i3 _raw_i4 h_320 h_325 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_320)
      have h_320 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) := h_320
      have h_321 : Litex.In _value_i3 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 h_320).1
            )
        )
      have h_322 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 h_320).2.1
            )
        )
      have h_323 : Litex.Le _value_i3 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 h_320).2.2
            )
        )
      have h_324 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_320)
            )
        )
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_325)
      have h_325 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) := h_325
      have h_326 : Litex.In _value_i4 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 h_325).1
            )
        )
      have h_327 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 h_325).2.1
            )
        )
      have h_328 : Litex.Le _value_i4 _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 h_325).2.2
            )
        )
      have h_329 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_325)
            )
        )
      change Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M))
      exact (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
    intro _litex_input _litex_domain
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
    exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
  exact (by
    let _equal_wd_1_0 := _object_w18
    let _equal_wd_1_1 := _object_w19
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15 _Host_i2 _rep_i2 _value_i2 h_17
          have h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_15)
                )
            )
          have h_18 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_17)
                )
            )
          let _object_w18 := (Litex.zeroMatrix _value_i1 _value_i2 h_15 h_17)
          let _object_w19 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.number (0 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
            have _litex_checked_return : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))) → M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17))) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → M.mem ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.number (0 : ℂ))) _raw_i3 _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i3 _raw_i4 h_320 h_325 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_320)
              have h_320 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) := h_320
              have h_321 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 h_320).1
                    )
                )
              have h_322 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 h_320).2.1
                    )
                )
              have h_323 : Litex.Le _value_i3 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 h_320).2.2
                    )
                )
              have h_324 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_320)
                    )
                )
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_325)
              have h_325 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) := h_325
              have h_326 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 h_325).1
                    )
                )
              have h_327 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 h_325).2.1
                    )
                )
              have h_328 : Litex.Le _value_i4 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 h_325).2.2
                    )
                )
              have h_329 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_325)
                    )
                )
              change Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M))
              exact (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
            exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w18
            let _equal_wd_1_1 := _object_w19
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w18;
                  let _equal_wd_1_1 := _object_w19;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show @Eq M.Value _ _ from Eq.refl _).trans (show Litex.Same _equal_wd_1_0 (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.number (0 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                    have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.number (0 : ℂ))) _raw_i5 _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i5 _raw_i6 h_669 h_674 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_669)
                      have h_669 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) := h_669
                      have h_670 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i5 h_669).1
                            )
                        )
                      have h_671 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i5 h_669).2.1
                            )
                        )
                      have h_672 : Litex.Le _value_i5 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i5 h_669).2.2
                            )
                        )
                      have h_673 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_669)
                            )
                        )
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_674)
                      have h_674 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) := h_674
                      have h_675 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i6 h_674).1
                            )
                        )
                      have h_676 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i6 h_674).2.1
                            )
                        )
                      have h_677 : Litex.Le _value_i6 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i6 h_674).2.2
                            )
                        )
                      have h_678 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_674)
                            )
                        )
                      change Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M))
                      exact (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                    exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) from by rfl)).trans (let _equal_wd_2_0 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.number (0 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                    have _litex_checked_return : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))) → M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17))) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.number (0 : ℂ))) _raw_i5 _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i5 _raw_i6 h_669 h_674 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_669)
                      have h_669 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) := h_669
                      have h_670 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i5 h_669).1
                            )
                        )
                      have h_671 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i5 h_669).2.1
                            )
                        )
                      have h_672 : Litex.Le _value_i5 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i5 h_669).2.2
                            )
                        )
                      have h_673 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_669)
                            )
                        )
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_674)
                      have h_674 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) := h_674
                      have h_675 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i6 h_674).1
                            )
                        )
                      have h_676 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i6 h_674).2.1
                            )
                        )
                      have h_677 : Litex.Le _value_i6 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i6 h_674).2.2
                            )
                        )
                      have h_678 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_674)
                            )
                        )
                      change Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M))
                      exact (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                    exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
                  let _equal_wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.number (0 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                    have _litex_checked_return : ∀ (_raw_i3 : M.Value) (_raw_i4 : M.Value), M.mem _raw_i3 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))) → M.mem _raw_i4 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17))) → ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) _raw_i3 _raw_i4) → M.mem ((fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.number (0 : ℂ))) _raw_i3 _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i3 _raw_i4 h_983 h_988 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_983)
                      have h_983 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) := h_983
                      have h_984 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 h_983).1
                            )
                        )
                      have h_985 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 h_983).2.1
                            )
                        )
                      have h_986 : Litex.Le _value_i3 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 h_983).2.2
                            )
                        )
                      have h_987 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_983)
                            )
                        )
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_988)
                      have h_988 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) := h_988
                      have h_989 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 h_988).1
                            )
                        )
                      have h_990 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 h_988).2.1
                            )
                        )
                      have h_991 : Litex.Le _value_i4 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 h_988).2.2
                            )
                        )
                      have h_992 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_988)
                            )
                        )
                      change Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M))
                      exact (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_15)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_17)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                    exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
                    let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_0
                    let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_1
                    exact (show Litex.Same _left _right from rfl)))))))
                )
            )
          exact h_1
        )
      )
  )

noncomputable def _object_i7 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
theorem h_1013 : Litex.Same (_object_i7 (M := M)) (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))))
      )
  )

noncomputable def _object_w21 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
let _litex_call_arg_1 := (Litex.number (M := M) (3 : ℂ));
Litex.callOn (Litex.zeroMatrixSignature ((Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))).val.rows ((Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))).val.cols) (_object_i7 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (let _litex_matrix := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix (_object_i7 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_1013 (M := M))).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
  exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
  exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (3 : ℂ) (1 : ℤ) (3 : ℤ) (3 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))), True.intro⟩))

theorem h_1014 : (by
  let _equal_wd_1_0 := (_object_w21 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w21 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (((show Litex.denote _equal_wd_1_0 = M.number 0 from (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ))))) (h_1013 (M := M))).trans (Litex.zeroMatrixCall (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))) (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)))) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        ))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ))))).mpr ⟨(Litex.callArguments2_mem_cart (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
          exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
          let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
          exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (3 : ℂ) (1 : ℤ) (3 : ℤ) (3 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))), True.intro⟩))).trans (show (M.number 0) = (Litex.denote (Litex.number (M := M) (0 : ℂ))) from rfl)).trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_zero_x5f_matrix_x5f_definition_x2f_statement_x2e_lit
