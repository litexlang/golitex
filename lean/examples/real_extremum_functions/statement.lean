import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_extremum_x5f_functions_x2f_statement_x2e_lit

universe u v11 v12 v13 v14
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.powerSet (Litex.R (M := M))))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.RealLeastUpperBoundValue M _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.supremumValue _raw_i2)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.powerSet (Litex.R (M := M)))) → M.mem _raw_i3 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.RealLeastUpperBoundValue M _raw_i2 _raw_i3)) _raw_i2 _raw_i3) → M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.supremumValue _raw_i2)) _raw_i2 _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
    intro _raw_i2 _raw_i3 h_58 h_60 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
    have h_58 : Litex.In _value_i2 (Litex.powerSet (Litex.R (M := M))) := h_58
    have h_59 : Litex.Subset _value_i2 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            ((Litex.inPowerSet_iff _value_i2 (Litex.R (M := M))).mp h_58)
          )
      )
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_60)
    have h_60 : Litex.In _value_i3 (Litex.R (M := M)) := h_60
    have h_1 : (Litex.RealLeastUpperBound _value_i2 _value_i3) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (Litex.RealLeastUpperBoundValue M _raw_i2 _raw_i3)
              exact h_1)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.supremum _value_i2 h_59 (Litex.realSupremumExistsOfCertificate _value_i2 _value_i3 h_1))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.supremum _value_i2 h_59 (Litex.realSupremumExistsOfCertificate _value_i2 _value_i3 h_1))
      exact (Litex.supremumInR _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.powerSet (Litex.R (M := M))))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.RealLeastUpperBoundValue M _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_102 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_103 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i6 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.powerSet (Litex.R (M := M))))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.RealGreatestLowerBoundValue M _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.infimumValue _raw_i7)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i7 : M.Value) (_raw_i8 : M.Value), M.mem _raw_i7 (Litex.denote (Litex.powerSet (Litex.R (M := M)))) → M.mem _raw_i8 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.RealGreatestLowerBoundValue M _raw_i7 _raw_i8)) _raw_i7 _raw_i8) → M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.infimumValue _raw_i7)) _raw_i7 _raw_i8) (Litex.denote (Litex.R (M := M))) := (by
    intro _raw_i7 _raw_i8 h_161 h_163 h_104
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_161)
    have h_161 : Litex.In _value_i7 (Litex.powerSet (Litex.R (M := M))) := h_161
    have h_162 : Litex.Subset _value_i7 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            ((Litex.inPowerSet_iff _value_i7 (Litex.R (M := M))).mp h_161)
          )
      )
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_163)
    have h_163 : Litex.In _value_i8 (Litex.R (M := M)) := h_163
    have h_104 : (Litex.RealGreatestLowerBound _value_i7 _value_i8) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (Litex.RealGreatestLowerBoundValue M _raw_i7 _raw_i8)
              exact h_104)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.infimum _value_i7 h_162 (Litex.realInfimumExistsOfCertificate _value_i7 _value_i8 h_104))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.infimum _value_i7 h_162 (Litex.realInfimumExistsOfCertificate _value_i7 _value_i8 h_104))
      exact (Litex.infimumInR _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.powerSet (Litex.R (M := M))))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.RealGreatestLowerBoundValue M _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_210 : Litex.In (_object_i6 (M := M)) (Litex.fnSet ((_object_i6 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i6 (M := M)))
      )
  )
theorem h_211 : Litex.Same (_object_i6 (M := M)) (_object_i6 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i6 (M := M)))
      )
  )

theorem h_214 : ∀ {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_239 : Litex.In _value_i11 (Litex.powerSet (Litex.R (M := M)))) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_241 : Litex.In _value_i12 (Litex.R (M := M))) (h_212 : (Litex.RealLeastUpperBound _value_i11 _value_i12)), (by
  let _object_w19 := (let _litex_call_arg_0 := _value_i11;
  let _litex_call_arg_1 := _value_i12;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_102 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
    exact h_239) h_241), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.RealLeastUpperBoundValue M _raw_i2 _raw_i3)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_212)⟩))
  exact (by
    let _equal_wd_1_0 := _object_w19
    exact Litex.Same _equal_wd_1_0 _value_i12)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i11 _rep_i11 _value_i11 h_239 _Host_i12 _rep_i12 _value_i12 h_241 h_212
          have h_240 : Litex.Subset _value_i11 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inPowerSet_iff _value_i11 (Litex.R (M := M))).mp h_239)
                )
            )
          let _object_w19 := (let _litex_call_arg_0 := _value_i11;
          let _litex_call_arg_1 := _value_i12;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_102 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
            exact h_239) h_241), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.RealLeastUpperBoundValue M _raw_i2 _raw_i3)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_212)⟩))
          have h_213 : (by
            let _equal_wd_1_0 := _object_w19
            exact Litex.Same _equal_wd_1_0 _value_i12) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w19;
                  (show Litex.Same _equal_wd_1_0 _value_i12 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])) = (Litex.denote _value_i12) from by
                    have _litex_residual : ((Litex.supremumValue (M := M)) (Litex.denote _value_i11)) = (Litex.denote _value_i12) := (Eq.trans (Litex.supremumValue_eq_certificate _value_i11 _value_i12 h_212) (show @Eq M.Value _ _ from Eq.refl _))
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])) = ((Litex.supremumValue (M := M)) (Litex.denote _value_i11)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i11;
                  let _wd_1_2 := _value_i12;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.powerSet (Litex.R (M := M))))
                    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.RealLeastUpperBoundValue M _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
                    exact h_239) h_241) (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.RealLeastUpperBoundValue M _raw_i2 _raw_i3)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_212)))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_103 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.supremumValue _raw_i2)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = ((Litex.supremumValue (M := M)) (Litex.denote _value_i11)); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.supremumValue _raw_i2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i11), (Litex.denote _value_i12)]) (M.number (1 : ℂ)) = (Litex.denote _value_i11) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i11), (Litex.denote _value_i12)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i11), (Litex.denote _value_i12)]) (M.number (2 : ℂ)) = (Litex.denote _value_i12) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i11), (Litex.denote _value_i12)] (1 : Fin 2)))))
                  ))).trans _litex_residual)))
                )
            )
          exact h_213
        )
      )
  )

theorem h_358 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_384 : Litex.In _value_i13 (Litex.powerSet (Litex.R (M := M)))) {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_386 : Litex.In _value_i14 (Litex.R (M := M))) (h_356 : (Litex.RealGreatestLowerBound _value_i13 _value_i14)), (by
  let _object_w22 := (let _litex_call_arg_0 := _value_i13;
  let _litex_call_arg_1 := _value_i14;
  Litex.callOn ((_object_i6 (M := M))).val.signature (_object_i6 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_210 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
    exact h_384) h_386), (Eq.mpr (congrArg₂ (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.RealGreatestLowerBoundValue M _raw_i7 _raw_i8)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_356)⟩))
  exact (by
    let _equal_wd_1_0 := _object_w22
    exact Litex.Same _equal_wd_1_0 _value_i14)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 h_384 _Host_i14 _rep_i14 _value_i14 h_386 h_356
          have h_385 : Litex.Subset _value_i13 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inPowerSet_iff _value_i13 (Litex.R (M := M))).mp h_384)
                )
            )
          let _object_w22 := (let _litex_call_arg_0 := _value_i13;
          let _litex_call_arg_1 := _value_i14;
          Litex.callOn ((_object_i6 (M := M))).val.signature (_object_i6 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_210 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
            exact h_384) h_386), (Eq.mpr (congrArg₂ (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.RealGreatestLowerBoundValue M _raw_i7 _raw_i8)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_356)⟩))
          have h_357 : (by
            let _equal_wd_1_0 := _object_w22
            exact Litex.Same _equal_wd_1_0 _value_i14) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w22;
                  (show Litex.Same _equal_wd_1_0 _value_i14 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (Litex.denote _value_i14) from by
                    have _litex_residual : ((Litex.infimumValue (M := M)) (Litex.denote _value_i13)) = (Litex.denote _value_i14) := (Eq.trans (Litex.infimumValue_eq_certificate _value_i13 _value_i14 h_356) (show @Eq M.Value _ _ from Eq.refl _))
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = ((Litex.infimumValue (M := M)) (Litex.denote _value_i13)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i6 (M := M));
                  let _wd_1_1 := _value_i13;
                  let _wd_1_2 := _value_i14;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.powerSet (Litex.R (M := M)))), (Litex.denote (Litex.R (M := M)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.powerSet (Litex.R (M := M))))
                    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.RealGreatestLowerBoundValue M _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
                    exact h_384) h_386) (Eq.mpr (congrArg₂ (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.RealGreatestLowerBoundValue M _raw_i7 _raw_i8)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_356)))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_211 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.infimumValue _raw_i7)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = ((Litex.infimumValue (M := M)) (Litex.denote _value_i13)); exact (congrArg₂ (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (Litex.infimumValue _raw_i7)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i13), (Litex.denote _value_i14)]) (M.number (1 : ℂ)) = (Litex.denote _value_i13) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i13), (Litex.denote _value_i14)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i13), (Litex.denote _value_i14)]) (M.number (2 : ℂ)) = (Litex.denote _value_i14) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i13), (Litex.denote _value_i14)] (1 : Fin 2)))))
                  ))).trans _litex_residual)))
                )
            )
          exact h_357
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_extremum_x5f_functions_x2f_statement_x2e_lit
