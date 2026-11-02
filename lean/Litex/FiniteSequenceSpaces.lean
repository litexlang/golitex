import Litex.FiniteSets

universe u v w x y

namespace Litex

theorem finiteSeqDomainOfNPosBound {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (n : Obj (M := M) β) (hn : In n Z) :
    F.sepValue (denote (NPos (M := M)))
      (fun x => ∃ r s : ℝ, x = M.number (r : ℂ) ∧ denote n = M.number (s : ℂ) ∧ r ≤ s) =
      finiteSeqDomain n := by
  apply F.ext _ _ (F.sep_isSet _ _ (isSet (NPos (M := M)))) (finiteSeqDomain_isSet n)
  intro x
  constructor
  · intro hx
    obtain ⟨hpos, r, s, hxr, hns, hrs⟩ := (F.sep_members _ _ x).mp hx
    obtain ⟨k, hxk, hkpos⟩ := integerWitnessOfNPos
      (semanticObject (M := M) x (M.member_isSet hpos)) hpos
    obtain ⟨q, hnq⟩ := (M.integer_members _).mp hn
    have hr : (k : ℝ) = r := Complex.ofReal_injective (by
      simpa only [Complex.ofReal_intCast] using M.number_injective (hxk.symm.trans hxr))
    have hs : (q : ℝ) = s := Complex.ofReal_injective (by
      simpa only [Complex.ofReal_intCast] using M.number_injective (hnq.symm.trans hns))
    have hkq : k ≤ q := by
      rw [← hr, ← hs] at hrs
      exact_mod_cast hrs
    apply (F.sep_members _ _ x).mpr
    refine ⟨?_, True.intro⟩
    apply (F.sep_members _ _ x).mpr
    refine ⟨(M.integer_members _).mpr ⟨k, hxk⟩, 1, q, k, ?_, hnq, hxk, ?_, hkq⟩
    · change M.number (1 : ℂ) = M.number ((1 : ℤ) : ℂ)
      norm_num
    · omega
  · intro hx
    obtain ⟨hi, _⟩ := (F.sep_members _ _ x).mp hx
    obtain ⟨hint, lo, up, k, hlo, hup, hxk, hlow, hupp⟩ := (F.sep_members _ _ x).mp hi
    have hlo' : lo = 1 := by
      change M.number (1 : ℂ) = M.number (lo : ℂ) at hlo
      exact_mod_cast M.number_injective hlo.symm
    subst lo
    have hkpos : 0 < k := by omega
    have hkn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
    have hkc : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by exact_mod_cast hkn
    have hnpos : M.mem x (denote (NPos (M := M))) := by
      apply (F.sep_members _ _ x).mpr
      refine ⟨(M.natural_members _).mpr ⟨k.toNat, hxk.trans (congrArg M.number hkc.symm)⟩,
        (k : ℝ), ?_, ?_⟩
      · simpa only [Complex.ofReal_intCast] using hxk
      · exact_mod_cast hkpos
    apply (F.sep_members _ _ x).mpr
    refine ⟨hnpos, (k : ℝ), (up : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using hxk
    · simpa only [Complex.ofReal_intCast] using hup
    · exact_mod_cast hupp

theorem integerRangeUpperSuccEqClosed {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b : ℤ) :
    F.sepValue (M.standard .integer)
      (RangeObj.condition ⟨number (a : ℂ), number ((b + 1 : ℤ) : ℂ)⟩) =
    F.sepValue (M.standard .integer)
      (ClosedRangeObj.condition ⟨number (a : ℂ), number (b : ℂ)⟩) := by
  apply F.ext _ _ (F.sep_isSet _ _ (M.standard_isSet .integer))
    (F.sep_isSet _ _ (M.standard_isSet .integer))
  intro x
  constructor
  · intro hx
    obtain ⟨hint, lo, up, k, hlo, hup, hxk, hlow, hupp⟩ := (F.sep_members _ _ x).mp hx
    have hlo' : lo = a := by
      change M.number (a : ℂ) = M.number (lo : ℂ) at hlo
      exact_mod_cast M.number_injective hlo.symm
    have hup' : up = b + 1 := by
      change M.number ((b + 1 : ℤ) : ℂ) = M.number (up : ℂ) at hup
      exact_mod_cast M.number_injective hup.symm
    subst lo
    subst up
    exact (F.sep_members _ _ x).mpr ⟨hint, a, b, k, rfl, rfl, hxk, hlow, by omega⟩
  · intro hx
    obtain ⟨hint, lo, up, k, hlo, hup, hxk, hlow, hupp⟩ := (F.sep_members _ _ x).mp hx
    have hlo' : lo = a := by
      change M.number (a : ℂ) = M.number (lo : ℂ) at hlo
      exact_mod_cast M.number_injective hlo.symm
    have hup' : up = b := by
      change M.number (b : ℂ) = M.number (up : ℂ) at hup
      exact_mod_cast M.number_injective hup.symm
    subst lo
    subst up
    exact (F.sep_members _ _ x).mpr ⟨hint, a, b + 1, k, rfl, rfl, hxk, hlow, by omega⟩

theorem finiteSeqDomainEmptyOfLengthZero {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (FiniteSeqSetObj (M := M) α β))
    (hz : denote s.val.length = M.number 0) :
    ∀ x, ¬ M.mem x (finiteSeqSignature s).domain := by
  intro x hx
  obtain ⟨hi, _⟩ := (F.sep_members _ _ x).mp hx
  obtain ⟨_, lo, up, k, hlo, hup, _, hlow, hupp⟩ := (F.sep_members _ _ x).mp hi
  have hlo' : lo = 1 := by
    change M.number (1 : ℂ) = M.number (lo : ℂ) at hlo
    exact_mod_cast M.number_injective hlo.symm
  have hup' : up = 0 := by
    change denote s.val.length = M.number (up : ℂ) at hup
    rw [hz] at hup
    exact_mod_cast M.number_injective hup.symm
  omega


theorem finiteSeqDomainCongr {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (h : Same a b) :
    finiteSeqDomain a = finiteSeqDomain b := by
  have condition : ClosedRangeObj.condition ⟨number 1, a⟩ =
      ClosedRangeObj.condition ⟨number 1, b⟩ := by
    funext z
    apply propext
    change (∃ lo up k : ℤ, denote (number (M := M) 1) = M.number (lo : ℂ) ∧
      denote a = M.number (up : ℂ) ∧ z = M.number (k : ℂ) ∧ lo ≤ k ∧ k ≤ up) ↔
      (∃ lo up k : ℤ, denote (number (M := M) 1) = M.number (lo : ℂ) ∧
      denote b = M.number (up : ℂ) ∧ z = M.number (k : ℂ) ∧ lo ≤ k ∧ k ≤ up)
    rw [show denote a = denote b from h]
  exact congrArg (fun C => F.sepValue (F.sepValue (M.standard .integer) C)
    (fun _ => True)) condition

theorem finiteSeqSameOfArgs {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (s : Obj (M := M) (FiniteSeqSetObj (M := M) α β))
    (t : Obj (M := M) (FiniteSeqSetObj (M := M) γ δ))
    (hc : Same s.val.carrier t.val.carrier) (hn : Same s.val.length t.val.length) :
    Same s t :=
  congrArg₂ F.fnSetValue (finiteSeqDomainCongr _ _ hn) hc

end Litex
