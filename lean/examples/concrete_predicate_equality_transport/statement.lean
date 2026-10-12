import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_concrete_x5f_predicate_x5f_equality_x5f_transport_x2f_statement_x2e_lit

universe u v1 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_2 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
  intro _raw_i4 h_71 h_41
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_71)
  have h_71 : Litex.In _value_i4 (Litex.R (M := M)) := h_71
  have h_41 : ((prop_1 (M := M)) _value_i4) :=
    (by
      change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))
      exact h_41)
  have h_72 : Litex.In _value_i4 (Litex.R (M := M)) :=
    (by rcases h_41 with ⟨h_2, h_1⟩; exact h_2)
  have h_75 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
    (by rcases h_41 with ⟨h_2, h_1⟩; exact h_1)
  change Litex.In (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.R (M := M))
  exact (by
    have _recorded_exp : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact Litex.powStructuralInR (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_71
  )))
theorem h_243 : Litex.In (_object_i3 (M := M)) (by
  have _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) _raw_i4) → True := by
    intro _raw_i4 h_175 h_41
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_175)
    have h_175 : Litex.In _value_i4 (Litex.R (M := M)) := h_175
    have h_41 : ((prop_1 (M := M)) _value_i4) :=
      (by
        change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))
        exact h_41)
    have h_176 : Litex.In _value_i4 (Litex.R (M := M)) :=
      (by rcases h_41 with ⟨h_2, h_1⟩; exact h_2)
    have h_179 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
      (by rcases h_41 with ⟨h_2, h_1⟩; exact h_1)
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))))) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_244 : Litex.Same (_object_i3 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
  intro _raw_i4 h_71 h_41
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_71)
  have h_71 : Litex.In _value_i4 (Litex.R (M := M)) := h_71
  have h_41 : ((prop_1 (M := M)) _value_i4) :=
    (by
      change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))
      exact h_41)
  have h_72 : Litex.In _value_i4 (Litex.R (M := M)) :=
    (by rcases h_41 with ⟨h_2, h_1⟩; exact h_2)
  have h_75 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
    (by rcases h_41 with ⟨h_2, h_1⟩; exact h_1)
  change Litex.In (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.R (M := M))
  exact (by
    have _recorded_exp : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact Litex.powStructuralInR (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_71
  ))) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_249 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_262 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_263 : Litex.In _value_i7 (Litex.R (M := M))) (h_245 : Litex.Same _value_i6 _value_i7) (h_246 : ((prop_1 (M := M)) _value_i6)), (((prop_1 (M := M)) _value_i7) ∧ Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (_object_i3 (M := M)) _value_i7 (h_243 (M := M)) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl _value_i6)).trans h_245) (Litex.sameRefl (Litex.R (M := M))) h_262) (show ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i7)) from by
  have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)) := h_246
  exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) _known_value)) (((Litex.sameRefl _value_i6)).trans h_245))) _known_citation
)) (Litex.powNatReal _value_i7 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl _value_i6)).trans h_245) (Litex.sameRefl (Litex.R (M := M))) h_262) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) :=
  (by
    intro _Host_i6 _rep_i6 _value_i6 h_262 _Host_i7 _rep_i7 _value_i7 h_263 h_245 h_246
    have h_264 : Litex.In _value_i6 (Litex.R (M := M)) :=
      (by rcases h_246 with ⟨h_2, h_1⟩; exact h_2)
    have h_267 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
      (by rcases h_246 with ⟨h_2, h_1⟩; exact h_1)
    have h_247 : ((prop_1 (M := M)) _value_i7) :=
      (show ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i7)) from by
        have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)) := h_246
        exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) _known_value)) (((Litex.sameRefl _value_i6)).trans h_245))) _known_citation
      )
    have h_370 : Litex.In _value_i7 (Litex.R (M := M)) :=
      (by rcases h_247 with ⟨h_2, h_1⟩; exact h_2)
    have h_373 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
      (by rcases h_247 with ⟨h_2, h_1⟩; exact h_1)
    have h_248 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (_object_i3 (M := M)) _value_i7 (h_243 (M := M)) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl _value_i6)).trans h_245) (Litex.sameRefl (Litex.R (M := M))) h_262) (show ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i7)) from by
      have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)) := h_246
      exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) _known_value)) (((Litex.sameRefl _value_i6)).trans h_245))) _known_citation
    )) (Litex.powNatReal _value_i7 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl _value_i6)).trans h_245) (Litex.sameRefl (Litex.R (M := M))) h_262) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) :=
      (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i7)))).trans (by
        let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (_object_i3 (M := M)) _value_i7 (h_243 (M := M)) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl _value_i6)).trans h_245) (Litex.sameRefl (Litex.R (M := M))) h_262) (show ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i7)) from by
          have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)) := h_246
          exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) _known_value)) (((Litex.sameRefl _value_i6)).trans h_245))) _known_citation
        ))
        let _litex_literal := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
          intro _raw_i4 h_71 h_41
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_71)
          have h_71 : Litex.In _value_i4 (Litex.R (M := M)) := h_71
          have h_41 : ((prop_1 (M := M)) _value_i4) :=
            (by
              change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))
              exact h_41)
          have h_72 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by rcases h_41 with ⟨h_2, h_1⟩; exact h_2)
          have h_75 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by rcases h_41 with ⟨h_2, h_1⟩; exact h_1)
          change Litex.In (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.R (M := M))
          exact (by
            have _recorded_exp : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact Litex.powStructuralInR (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_71
          ))) _value_i7 (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
          intro _raw_i4 h_71 h_41
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_71)
          have h_71 : Litex.In _value_i4 (Litex.R (M := M)) := h_71
          have h_41 : ((prop_1 (M := M)) _value_i4) :=
            (by
              change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))
              exact h_41)
          have h_72 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by rcases h_41 with ⟨h_2, h_1⟩; exact h_2)
          have h_75 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by rcases h_41 with ⟨h_2, h_1⟩; exact h_1)
          change Litex.In (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.R (M := M))
          exact (by
            have _recorded_exp : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact Litex.powStructuralInR (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_71 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_71
          )))) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl _value_i6)).trans h_245) (Litex.sameRefl (Litex.R (M := M))) h_262) (show ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i7)) from by
          have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)) := h_246
          exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ (_predicate_witness : (M.mem _known_argument_0 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _known_argument_0 = M.number (_s : ℂ) ∧ _r ≤ _s))) _known_value)) (((Litex.sameRefl _value_i6)).trans h_245))) _known_citation
        ))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i3 (M := M)))).trans (h_244 (M := M))) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i4 = M.number (_s : ℂ) ∧ _r ≤ _s))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (Litex.denote _value_i7) (M.number (2 : ℂ))) from rfl))
      ))).trans (Litex.sameRefl (Litex.powNatReal _value_i7 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inOfSame _value_i6 _value_i7 (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl _value_i6)).trans h_245) (Litex.sameRefl (Litex.R (M := M))) h_262) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))
    exact (And.intro h_247 h_248)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_concrete_x5f_predicate_x5f_equality_x5f_transport_x2f_statement_x2e_lit
