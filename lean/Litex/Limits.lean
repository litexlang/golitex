import Litex.RealBounds

universe u v w x r

namespace Litex

def SequenceOrderValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (strict reverse : Bool) (a : M.Value) : Prop :=
  ∀ m, M.mem m (denote (NPos (M := M))) →
    ∀ n, M.mem n (denote (NPos (M := M))) →
      (∃ r s : ℝ, m = M.number (r : ℂ) ∧ n = M.number (s : ℂ) ∧
        (if strict then r < s else r ≤ s)) →
      ∃ r s : ℝ,
        F.callValue a (if reverse then n else m) = M.number (r : ℂ) ∧
        F.callValue a (if reverse then m else n) = M.number (s : ℂ) ∧
        (if strict then r < s else r ≤ s)

/-- Consume the source's universal proof at its own two host universe levels. -/
theorem sequenceOrderOfForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (strict reverse : Bool) (a : Obj (M := M) α)
    (h : ∀ {β : Type w} [Representation M β], (m : Obj (M := M) β) → In m NPos →
      ∀ {γ : Type x} [Representation M γ], (n : Obj (M := M) γ) → In n NPos →
      (∃ r s : ℝ, denote m = M.number (r : ℂ) ∧ denote n = M.number (s : ℂ) ∧
        (if strict then r < s else r ≤ s)) →
      ∃ r s : ℝ,
        F.callValue (denote a) (if reverse then denote n else denote m) = M.number (r : ℂ) ∧
        F.callValue (denote a) (if reverse then denote m else denote n) = M.number (s : ℂ) ∧
        (if strict then r < s else r ≤ s)) : SequenceOrderValue M strict reverse (denote a) :=
  forallMembersOfRepresentations NPos (fun m hm =>
    forallMembersOfRepresentations NPos (fun n hn => h m hm n hn))

def SequenceNondecreasingValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := SequenceOrderValue M false false a

def SequenceNondecreasing {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceNondecreasingValue M (denote a)

def SequenceNonincreasingValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := SequenceOrderValue M false true a

def SequenceNonincreasing {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceNonincreasingValue M (denote a)

def SequenceStrictlyIncreasingValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := SequenceOrderValue M true false a

def SequenceStrictlyIncreasing {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceStrictlyIncreasingValue M (denote a)

def SequenceStrictlyDecreasingValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := SequenceOrderValue M true true a

def SequenceStrictlyDecreasing {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceStrictlyDecreasingValue M (denote a)

def SequenceBoundedAboveValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := RealBoundedAboveValue M (FunctionSemantics.rangeValue a)

def SequenceBoundedAbove {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceBoundedAboveValue M (denote a)

def SequenceBoundedBelowValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := RealBoundedBelowValue M (FunctionSemantics.rangeValue a)

def SequenceBoundedBelow {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceBoundedBelowValue M (denote a)

def SequenceBoundedValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := RealBoundedValue M (FunctionSemantics.rangeValue a)

def SequenceBounded {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceBoundedValue M (denote a)

end Litex

namespace Litex

theorem negationWeakOrder {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (NegObj (M := M) α)) (q : Obj (M := M) (NegObj (M := M) β))
    (h : Le q.val.arg p.val.arg) : Le p q := by
  obtain ⟨r,s,hr,hs,h⟩ := h
  refine ⟨-s,-r,?_,?_,neg_le_neg h⟩
  · change M.negValue (denote p.val.arg) = _
    rw [hs,M.neg_numbers,Complex.ofReal_neg]
  · change M.negValue (denote q.val.arg) = _
    rw [hr,M.neg_numbers,Complex.ofReal_neg]

theorem negationStrictOrder {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (NegObj (M := M) α)) (q : Obj (M := M) (NegObj (M := M) β))
    (h : Lt q.val.arg p.val.arg) : Lt p q := by
  obtain ⟨r,s,hr,hs,h⟩ := h
  refine ⟨-s,-r,?_,?_,neg_lt_neg h⟩
  · change M.negValue (denote p.val.arg) = _
    rw [hs,M.neg_numbers,Complex.ofReal_neg]
  · change M.negValue (denote q.val.arg) = _
    rw [hr,M.neg_numbers,Complex.ofReal_neg]
end Litex


namespace Litex

/-- The source tail keeps its positive-natural carrier and cutoff comparison. -/
def sequenceTailValue {M : Semantics.{u}} [SetSemantics M] (cutoff : M.Value) : M.Value :=
  SetSemantics.sepValue (denote (NPos (M := M))) (fun n =>
    ∃ _ : M.mem n (denote (NPos (M := M))),
      ∃ r s : ℝ, cutoff = M.number (r : ℂ) ∧ n = M.number (s : ℂ) ∧ r ≤ s)

def sequenceEpsilonBallValue {M : Semantics.{u}} [SetSemantics M]
    (value epsilon : M.Value) : M.Value :=
  SetSemantics.sepValue (denote (R (M := M))) (fun y =>
    ∃ _ : M.mem y (denote (R (M := M))),
      ∃ r s : ℝ, absValue (M.subValue y value) = M.number (r : ℂ) ∧
        epsilon = M.number (s : ℂ) ∧ r < s)

def SequenceLimitTailValue (M : Semantics.{u}) [FunctionSemantics M]
    (a value epsilon cutoff : M.Value) : Prop :=
  ∀ n, M.mem n (sequenceTailValue cutoff) →
    M.mem n (FunctionSemantics.preimageValue a
      (fun y => M.mem y (sequenceEpsilonBallValue value epsilon)))

def SequenceCauchyTailValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (a epsilon cutoff : M.Value) : Prop :=
  ∀ p, M.mem p (FiniteFunction.cartValue ![sequenceTailValue cutoff, sequenceTailValue cutoff]) →
    M.mem p (SetSemantics.sepValue
      (FiniteFunction.cartValue ![denote (NPos (M := M)), denote (NPos (M := M))])
      (fun q => ∃ _ : M.mem q (FiniteFunction.cartValue
        ![denote (NPos (M := M)), denote (NPos (M := M))]),
        ∃ r s : ℝ,
          absValue (M.subValue
            (F.callValue a (F.callValue q (M.number 1)))
            (F.callValue a (F.callValue q (M.number 2)))) = M.number (r : ℂ) ∧
          epsilon = M.number (s : ℂ) ∧ r < s))

def HasSequenceLimitValue (M : Semantics.{u}) [FunctionSemantics M]
    (a value : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
      SequenceLimitTailValue M a value epsilon (denote cutoff)

def HasSequenceLimit {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β) : Prop :=
  HasSequenceLimitValue M (denote a) (denote value)

def SequenceCauchyValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
      SequenceCauchyTailValue M a epsilon (denote cutoff)

def SequenceCauchy {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceCauchyValue M (denote a)

def SequenceConvergentValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop :=
  ∃ value : Obj (M := M) M.Value, ∃ _ : In value R,
    HasSequenceLimitValue M a (denote value)

def SequenceConvergent {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceConvergentValue M (denote a)

theorem sequenceLimitOfForall {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β)
    (h : ∀ {γ : Type x} [Representation M γ], (epsilon : Obj (M := M) γ) →
      In epsilon RPos → ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
        SequenceLimitTailValue M (denote a) (denote value) (denote epsilon) (denote cutoff)) :
    HasSequenceLimit a value := forallMembersOfRepresentations RPos h

theorem sequenceCauchyOfForall {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (h : ∀ {γ : Type w} [Representation M γ], (epsilon : Obj (M := M) γ) →
      In epsilon RPos → ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
        SequenceCauchyTailValue M (denote a) (denote epsilon) (denote cutoff)) :
    SequenceCauchy a := forallMembersOfRepresentations RPos h
end Litex

namespace Litex

-- A single tail bound yields the native metric bound at a positive natural index.
theorem sequenceLimitAtIndex {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (r epsilon : ℝ) (cutoff : Obj (M := M) M.Value)
    (n : ℕ) (hn : 0 < n)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hcut : In cutoff NPos)
    (horder : NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) ≤ n)
    (htail : SequenceLimitTailValue M a (M.number (r : ℂ)) (M.number (epsilon : ℂ)) (denote cutoff)) :
    ∃ v : ℝ, F.callValue a (M.number (n : ℂ)) = M.number (v : ℂ) ∧ |v-r| < epsilon := by
  let cut := NativeBridge.asNat cutoff (inNPos_natural cutoff hcut)
  have hcutval : denote cutoff = M.number ((cut : ℕ) : ℂ) := NativeBridge.asNat_spec cutoff (inNPos_natural cutoff hcut)
  have hnmem : M.mem (M.number (n : ℂ)) (denote (NPos (M := M))) := numberInNPosOfEq (M := M) (n : ℂ) n rfl hn
  have htailmem : M.mem (M.number (n : ℂ)) (sequenceTailValue (denote cutoff)) := by
    apply (F.sep_members _ _ _).mpr
    refine ⟨hnmem, hnmem, (cut : ℝ), (n : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_natCast] using hcutval
    · simp only [Complex.ofReal_natCast]
    · exact_mod_cast horder
  have himage := htail _ htailmem
  have hdomain := isSet (NPos (M := M))
  have hp := ((FunctionSemantics.preimage_mem_iff (fun y => M.mem y (sequenceEpsilonBallValue (M.number (r : ℂ)) (M.number (epsilon : ℂ)))) hdomain hf).mp himage).2
  obtain ⟨hvR, _, t, e, hdist, heps, hlt⟩ := (F.sep_members _ _ _).mp hp
  obtain ⟨v, hv⟩ := (M.real_members _).mp hvR
  have he : e = epsilon := Complex.ofReal_injective (M.number_injective heps).symm
  have ht : t = |v-r| := by
    have hden : absValue (M.subValue (F.callValue a (M.number (n : ℂ))) (M.number (r : ℂ))) = M.number ((|v-r| : ℝ) : ℂ) := by
      rw [hv, M.sub_numbers, ← Complex.ofReal_sub, absValue_number]
    exact Complex.ofReal_injective (M.number_injective (hdist.symm.trans hden))
  refine ⟨v, hv, ?_⟩
  simpa only [ht, he] using hlt

theorem sequenceLimitUnique {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (r s : ℝ)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hr : HasSequenceLimitValue M a (M.number (r : ℂ)))
    (hs : HasSequenceLimitValue M a (M.number (s : ℂ))) : r = s := by
  by_contra hne
  have hd : 0 < |r-s| := abs_pos.mpr (sub_ne_zero.mpr hne)
  let epsilon : ℝ := |r-s| / 2
  have heps : 0 < epsilon := by dsimp [epsilon]; linarith
  have hepsmem : M.mem (M.number (epsilon : ℂ)) (denote (RPos (M := M))) := numberInRPos epsilon heps
  obtain ⟨c1,hc1,ht1⟩ := hr (M.number (epsilon : ℂ)) hepsmem
  obtain ⟨c2,hc2,ht2⟩ := hs (M.number (epsilon : ℂ)) hepsmem
  let n1 := NativeBridge.asNat c1 (inNPos_natural c1 hc1)
  let n2 := NativeBridge.asNat c2 (inNPos_natural c2 hc2)
  let n := Nat.max n1 n2 + 1
  have hn : 0 < n := by dsimp [n]; omega
  have h1 : n1 ≤ n := Nat.le_trans (Nat.le_max_left n1 n2) (Nat.le_succ _)
  have h2 : n2 ≤ n := Nat.le_trans (Nat.le_max_right n1 n2) (Nat.le_succ _)
  obtain ⟨v,hv,hvr⟩ := sequenceLimitAtIndex a r epsilon c1 n hn hf hc1 h1 ht1
  obtain ⟨w,hw,hws⟩ := sequenceLimitAtIndex a s epsilon c2 n hn hf hc2 h2 ht2
  have heq : v = w := Complex.ofReal_injective (M.number_injective (hv.symm.trans hw))
  subst w
  have htri : |r-s| ≤ |r-v| + |v-s| := abs_sub_le r v s
  rw [abs_sub_comm r v] at htri
  dsimp [epsilon] at hvr hws
  linarith
end Litex
namespace Litex

noncomputable def sequenceLimitValue {M : Semantics.{u}} [FunctionSemantics M] (a : M.Value) : M.Value := by
  classical
  exact if h : SequenceConvergentValue M a then denote (Classical.choose h) else M.number 0

theorem sequenceLimitValueOfCandidate {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (r : ℝ)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hr : HasSequenceLimitValue M a (M.number (r : ℂ))) :
    sequenceLimitValue a = M.number (r : ℂ) := by
  classical
  have hm : M.mem (M.number (r : ℂ)) (denote (R (M := M))) := (M.real_members _).mpr ⟨r,rfl⟩
  let v : Obj (M := M) M.Value := semanticObject (M.number (r : ℂ)) (M.member_isSet hm)
  have hc : SequenceConvergentValue M a := ⟨v, hm, hr⟩
  let selected := Classical.choose hc
  have hs := Classical.choose_spec hc
  obtain ⟨s, hselected⟩ := (M.real_members _).mp hs.1
  have heq : s = r := sequenceLimitUnique a s r hf (hselected ▸ hs.2) hr
  unfold sequenceLimitValue
  rw [dif_pos hc]
  exact hselected.trans (congrArg (fun x : ℝ => M.number (x : ℂ)) heq)

structure SequenceLimitObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  sequence : Obj (M := M) α

noncomputable instance sequenceLimitRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] : Representation M (SequenceLimitObj (M := M) α) where
  wd p := M.mem (denote p.sequence) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))) ∧
    SequenceConvergentValue M (denote p.sequence)
  denote p := sequenceLimitValue (denote p.sequence)
  wd_isSet {p} hp := by
    classical
    unfold sequenceLimitValue
    rw [dif_pos hp.2]
    exact M.member_isSet (Classical.choose_spec hp.2).1
end Litex
namespace Litex

noncomputable def sequenceLimit {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hc : SequenceConvergentValue M (denote a)) : Obj (M := M) (SequenceLimitObj (M := M) α) :=
  ⟨⟨a⟩, ha, hc⟩

theorem sequenceConvergentOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β) (hR : In value R)
    (h : HasSequenceLimit a value) : SequenceConvergentValue M (denote a) := by
  let v : Obj (M := M) M.Value := semanticObject (denote value) (isSet value)
  exact ⟨v, hR, h⟩

theorem sequenceLimitEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (SequenceLimitObj (M := M) α)) (value : Obj (M := M) β)
    (hR : In value R) (h : HasSequenceLimit p.val.sequence value) : Same p value := by
  let r := NativeBridge.asReal value hR
  have hr := NativeBridge.asReal_spec value hR
  change sequenceLimitValue (denote p.val.sequence) = denote value
  exact (sequenceLimitValueOfCandidate (denote p.val.sequence) r p.wd.1 (hr ▸ h)).trans hr.symm

theorem sequenceLimitInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) (SequenceLimitObj (M := M) α)) : In p R := by
  classical
  change M.mem (sequenceLimitValue (denote p.val.sequence)) (denote R)
  unfold sequenceLimitValue
  rw [dif_pos p.wd.2]
  exact (Classical.choose_spec p.wd.2).1
end Litex

namespace Litex
theorem unguardedFunctionDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (D B : M.Value) (hD : M.isSet D) (hB : M.isSet B)
    (h : In a (fnSet (FunctionSignature.withGuard D B hD hB (fun _ => True)))) :
    M.mem (denote a) (F.fnSetValue D B) := by
  have heq : F.sepValue D (fun _ => True) = D := by
    apply F.ext _ _ (F.sep_isSet D _ hD) hD
    intro x
    simp only [F.sep_members, and_true]
  change M.mem (denote a) (F.fnSetValue (F.sepValue D (fun _ => True)) B) at h
  simpa only [heq] using h
end Litex

namespace Litex
theorem sequenceLimitCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (v : Obj (M := M) β) (w : Obj (M := M) γ)
    (hdom : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : In v R) (hw : In w R) (h1 : HasSequenceLimit a v) (h2 : HasSequenceLimit a w) : Same v w := by
  let r := NativeBridge.asReal v hv
  let s := NativeBridge.asReal w hw
  have hr := NativeBridge.asReal_spec v hv
  have hs := NativeBridge.asReal_spec w hw
  have heq : r = s := sequenceLimitUnique (denote a) r s hdom (hr ▸ h1) (hs ▸ h2)
  exact hr.trans ((congrArg (fun x : ℝ => M.number (x : ℂ)) heq).trans hs.symm)
end Litex


namespace Litex

namespace FunctionSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- The exact graph domain is independent of the signature used to certify it. -/
noncomputable def domainValue (f : M.Value) : M.Value := preimageValue f (fun _ => True)

theorem domainValue_eq {D B f : M.Value} (hD : M.isSet D)
    (hf : M.mem f (F.fnSetValue D B)) : domainValue f = D := by
  apply F.ext _ _ (preimage_spec (fun _ => True) hD hf).1 hD
  intro x
  exact (preimage_mem_iff (fun _ => True) hD hf).trans ⟨And.left, fun hx => ⟨hx, True.intro⟩⟩
end FunctionSemantics

inductive FiniteLimitSide where
  | both | left | right

def finiteLimitDistance (side : FiniteLimitSide) (point input : ℝ) : ℝ :=
  match side with
  | .both => |input - point|
  | .left => point - input
  | .right => input - point

/-- The punctured domain must have points arbitrarily near the approach point. -/
def FiniteFunctionAccumulationValue (M : Semantics.{u}) [FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (point : ℝ) : Prop :=
  ∀ radius : ℝ, 0 < radius → ∃ input : ℝ,
    M.mem (M.number (input : ℂ)) (FunctionSemantics.domainValue f) ∧
      0 < finiteLimitDistance side point input ∧ finiteLimitDistance side point input < radius

def FiniteFunctionEpsilonValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (point value : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
    ∀ input : ℝ, M.mem (M.number (input : ℂ)) (F.domainValue f) →
      0 < finiteLimitDistance side point input → finiteLimitDistance side point input < delta →
      ∃ output : ℝ, F.callValue f (M.number (input : ℂ)) = M.number (output : ℂ) ∧
        |output - value| < epsilon

def HasFiniteFunctionLimitValue (M : Semantics.{u}) [FunctionSemantics M]
    (side : FiniteLimitSide) (f point value : M.Value) : Prop :=
  ∃ p l : ℝ, point = M.number (p : ℂ) ∧ value = M.number (l : ℂ) ∧
    FiniteFunctionAccumulationValue M side f p ∧ FiniteFunctionEpsilonValue M side f p l

def HasFiniteFunctionLimit {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (value : Obj (M := M) γ) : Prop :=
  HasFiniteFunctionLimitValue M side (denote f) (denote point) (denote value)

theorem finiteFunctionLimitUnique {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (point r s : ℝ)
    (ha : FiniteFunctionAccumulationValue M side f point)
    (hr : FiniteFunctionEpsilonValue M side f point r)
    (hs : FiniteFunctionEpsilonValue M side f point s) : r = s := by
  by_contra hne
  have hdist : 0 < |r-s| := abs_pos.mpr (sub_ne_zero.mpr hne)
  let epsilon := |r-s| / 2
  have he : 0 < epsilon := by dsimp [epsilon]; linarith
  obtain ⟨d1, hd1, h1⟩ := hr epsilon he
  obtain ⟨d2, hd2, h2⟩ := hs epsilon he
  obtain ⟨input, hinput, hpositive, hnear⟩ := ha (Min.min d1 d2) (lt_min hd1 hd2)
  obtain ⟨u, hu, hur⟩ := h1 input hinput hpositive (lt_of_lt_of_le hnear (min_le_left _ _))
  obtain ⟨v, hv, hvs⟩ := h2 input hinput hpositive (lt_of_lt_of_le hnear (min_le_right _ _))
  have huv : u = v := Complex.ofReal_injective (M.number_injective (hu.symm.trans hv))
  subst v
  have htriangle := abs_sub_le r u s
  rw [abs_sub_comm r u] at htriangle
  dsimp [epsilon] at hur hvs
  linarith

theorem finiteFunctionLimitCandidatesEqual {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (a : Obj (M := M) γ) (b : Obj (M := M) δ)
    (ha : HasFiniteFunctionLimit side f point a) (hb : HasFiniteFunctionLimit side f point b) :
    Same a b := by
  obtain ⟨p, r, hp, hr, hacc, her⟩ := ha
  obtain ⟨q, s, hq, hs, _, hes⟩ := hb
  have hpq : p = q := Complex.ofReal_injective (M.number_injective (hp.symm.trans hq))
  subst q
  have hrs := finiteFunctionLimitUnique side (denote f) p r s hacc her hes
  exact hr.trans ((congrArg (fun z : ℝ => M.number (z : ℂ)) hrs).trans hs.symm)

def FiniteFunctionConvergentValue (M : Semantics.{u}) [FunctionSemantics M]
    (side : FiniteLimitSide) (f point : M.Value) : Prop :=
  ∃ value : ℝ, HasFiniteFunctionLimitValue M side f point (M.number (value : ℂ))

noncomputable def finiteFunctionLimitValue {M : Semantics.{u}} [FunctionSemantics M]
    (side : FiniteLimitSide) (f point : M.Value) : M.Value := by
  classical
  let selected : ℝ := if h : FiniteFunctionConvergentValue M side f point
    then Classical.choose h else 0
  exact M.number (selected : ℂ)

def RealFunctionValue (M : Semantics.{u}) [FunctionSemantics M] (f : M.Value) : Prop :=
  ∃ signature : FunctionSignature M,
    M.mem f (FunctionSemantics.fnSetValue signature.domain signature.output) ∧
    (∀ x, M.mem x signature.domain → M.mem x (denote (R (M := M)))) ∧
    (∀ y, M.mem y signature.output → M.mem y (denote (R (M := M))))

structure FiniteFunctionLimitObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  side : FiniteLimitSide

noncomputable instance finiteFunctionLimitRepresentation {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (FiniteFunctionLimitObj (M := M) α β) where
  wd p := RealFunctionValue M (denote p.function) ∧ In p.point R ∧
    FiniteFunctionConvergentValue M p.side (denote p.function) (denote p.point)
  denote p := finiteFunctionLimitValue p.side (denote p.function) (denote p.point)
  wd_isSet {p} _ := by
    unfold finiteFunctionLimitValue
    exact M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def finiteFunctionLimit {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (hf : RealFunctionValue M (denote f)) (hp : In point R)
    (hc : FiniteFunctionConvergentValue M side (denote f) (denote point)) :
    Obj (M := M) (FiniteFunctionLimitObj (M := M) α β) := ⟨⟨f, point, side⟩, hf, hp, hc⟩

theorem finiteFunctionConvergentOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (value : Obj (M := M) γ) (h : HasFiniteFunctionLimit side f point value) :
    FiniteFunctionConvergentValue M side (denote f) (denote point) := by
  obtain ⟨p, l, hp, hl, ha, he⟩ := h
  exact ⟨l, p, l, hp, rfl, ha, he⟩

theorem finiteFunctionLimitEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteFunctionLimitObj (M := M) α β)) (value : Obj (M := M) γ)
    (h : HasFiniteFunctionLimit p.val.side p.val.function p.val.point value) : Same p value := by
  classical
  have hc := p.wd.2.2
  have chosen := Classical.choose_spec hc
  have heq := finiteFunctionLimitCandidatesEqual p.val.side p.val.function p.val.point
    (number (M := M) ((Classical.choose hc : ℝ) : ℂ)) value chosen h
  change finiteFunctionLimitValue p.val.side (denote p.val.function) (denote p.val.point) = denote value
  unfold finiteFunctionLimitValue
  rw [dif_pos hc]
  exact heq

theorem finiteFunctionLimitInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteFunctionLimitObj (M := M) α β)) : In p R := by
  classical
  change M.mem (finiteFunctionLimitValue p.val.side (denote p.val.function) (denote p.val.point)) _
  unfold finiteFunctionLimitValue
  exact (M.real_members _).mpr ⟨_, rfl⟩

end Litex


namespace Litex

def RealLtValue (M : Semantics.{u}) (a b : M.Value) : Prop :=
  ∃ r s : ℝ, a = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r < s

theorem realLtValue_numbers {M : Semantics.{u}} (a b : ℝ) :
    RealLtValue M (M.number (a : ℂ)) (M.number (b : ℂ)) ↔ a < b := by
  constructor
  · rintro ⟨r, s, hr, hs, h⟩
    have har : a = r := Complex.ofReal_injective (M.number_injective hr)
    have hbs : b = s := Complex.ofReal_injective (M.number_injective hs)
    simpa only [har, hbs] using h
  · exact fun h => ⟨a, b, rfl, rfl, h⟩

noncomputable def finiteLimitDistanceValue {M : Semantics.{u}}
    (side : FiniteLimitSide) (point input : M.Value) : M.Value :=
  match side with
  | .both => absValue (M.subValue input point)
  | .left => M.subValue point input
  | .right => M.subValue input point

theorem finiteLimitDistanceValue_numbers {M : Semantics.{u}}
    (side : FiniteLimitSide) (point input : ℝ) :
    finiteLimitDistanceValue side (M.number (point : ℂ)) (M.number (input : ℂ)) =
      M.number ((finiteLimitDistance side point input : ℝ) : ℂ) := by
  cases side <;> simp only [finiteLimitDistanceValue, finiteLimitDistance, M.sub_numbers,
    ← Complex.ofReal_sub, absValue_number]

noncomputable def finiteLimitNeighborhoodValue {M : Semantics.{u}} [SetSemantics M]
    (side : FiniteLimitSide) (domain point radius : M.Value) : M.Value :=
  SetSemantics.sepValue domain (fun x => ∃ _ : M.mem x domain,
    RealLtValue M (M.number 0) (finiteLimitDistanceValue side point x) ∧
    RealLtValue M (finiteLimitDistanceValue side point x) radius)

def FiniteLimitAccumulationClauseValue (M : Semantics.{u}) [SetSemantics M]
    (side : FiniteLimitSide) (domain point radius : M.Value) : Prop :=
  ∃ input : Obj (M := M) M.Value, ∃ _ : M.mem (denote input) domain,
    RealLtValue M (M.number 0) (finiteLimitDistanceValue side point (denote input)) ∧
    RealLtValue M (finiteLimitDistanceValue side point (denote input)) radius

def FiniteLimitEpsilonClauseValue (M : Semantics.{u}) [FunctionSemantics M]
    (side : FiniteLimitSide) (f domain point value epsilon : M.Value) : Prop :=
  ∃ delta : Obj (M := M) M.Value, ∃ _ : In delta RPos,
    ∀ input, M.mem input (finiteLimitNeighborhoodValue side domain point (denote delta)) →
      M.mem input (FunctionSemantics.preimageValue f
        (fun y => M.mem y (sequenceEpsilonBallValue value epsilon)))

theorem finiteFunctionConvergentOfExistence {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (h : ∃ value : Obj (M := M) M.Value, ∃ _ : In value R,
      HasFiniteFunctionLimit side f point value) :
    FiniteFunctionConvergentValue M side (denote f) (denote point) := by
  obtain ⟨value, _, h⟩ := h
  exact finiteFunctionConvergentOfCandidate side f point value h

theorem finiteFunctionLimitOfForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (value : Obj (M := M) γ) (domain : Obj (M := M) δ)
    (hf : RealFunctionValue M (denote f))
    (hD : denote domain = F.domainValue (denote f))
    (hp : In point R) (hv : In value R)
    (ha : ∀ {σ : Type z} [Representation M σ], (radius : Obj (M := M) σ) →
      In radius RPos → FiniteLimitAccumulationClauseValue M side (denote domain) (denote point) (denote radius))
    (he : ∀ {σ : Type t} [Representation M σ], (epsilon : Obj (M := M) σ) →
      In epsilon RPos → FiniteLimitEpsilonClauseValue M side (denote f) (denote domain) (denote point) (denote value) (denote epsilon)) :
    HasFiniteFunctionLimit side f point value := by
  let p := NativeBridge.asReal point hp
  let l := NativeBridge.asReal value hv
  have hpvalue : denote point = M.number (p : ℂ) := NativeBridge.asReal_spec point hp
  have hlvalue : denote value = M.number (l : ℂ) := NativeBridge.asReal_spec value hv
  have ha := forallMembersOfRepresentations RPos ha
  have he := forallMembersOfRepresentations RPos he
  obtain ⟨signature, hfn, hinput, _⟩ := hf
  have hdomain : denote domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  refine ⟨p, l, hpvalue, hlvalue, ?_, ?_⟩
  · intro radius hradius
    obtain ⟨input, hmem, hpositive, hnear⟩ := ha (M.number (radius : ℂ)) (numberInRPos radius hradius)
    obtain ⟨x, hx⟩ := (M.real_members (denote input)).mp (hinput _ (hdomain ▸ hmem))
    refine ⟨x, ?_, ?_, ?_⟩
    · rw [← hx, ← hD]
      exact hmem
    · rw [hpvalue, hx, finiteLimitDistanceValue_numbers] at hpositive
      exact (realLtValue_numbers 0 _).mp hpositive
    · rw [hpvalue, hx, finiteLimitDistanceValue_numbers] at hnear
      exact (realLtValue_numbers _ radius).mp hnear
  · intro epsilon hepsilon
    obtain ⟨delta, hdelta, hcontrol⟩ := he (M.number (epsilon : ℂ)) (numberInRPos epsilon hepsilon)
    let d := NativeBridge.asReal delta (inRPos_real delta hdelta)
    have hdvalue : denote delta = M.number (d : ℂ) := NativeBridge.asReal_spec delta (inRPos_real delta hdelta)
    have hd : 0 < d := (NativeBridge.lt_iff_ofDenoteReal (number 0) delta 0 d rfl hdvalue).mp (inRPos_positive delta hdelta)
    refine ⟨d, hd, ?_⟩
    intro x hx hpositive hnear
    have hxD : M.mem (M.number (x : ℂ)) (denote domain) := hD ▸ hx
    have hn : M.mem (M.number (x : ℂ)) (finiteLimitNeighborhoodValue side (denote domain) (denote point) (denote delta)) := by
      apply (F.sep_members _ _ _).mpr
      refine ⟨hxD, hxD, ?_, ?_⟩
      · rw [hpvalue, finiteLimitDistanceValue_numbers]
        exact (realLtValue_numbers 0 _).mpr hpositive
      · rw [hpvalue, hdvalue, finiteLimitDistanceValue_numbers]
        exact (realLtValue_numbers _ d).mpr hnear
    have image := ((F.preimage_mem_iff (fun y => M.mem y (sequenceEpsilonBallValue (denote value) (M.number (epsilon : ℂ)))) signature.domain_isSet hfn).mp (hcontrol _ hn)).2
    obtain ⟨hyR, _, hless⟩ := (F.sep_members _ _ _).mp image
    obtain ⟨y, hy⟩ := (M.real_members _).mp hyR
    refine ⟨y, hy, ?_⟩
    change RealLtValue M (absValue (M.subValue (F.callValue (denote f) (M.number (x : ℂ))) (denote value))) (M.number (epsilon : ℂ)) at hless
    rw [hy, hlvalue, M.sub_numbers, ← Complex.ofReal_sub, absValue_number] at hless
    exact (realLtValue_numbers _ epsilon).mp hless

end Litex


namespace Litex

theorem divByGtOneLessSelf {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (DivObj (M := M) α β))
    (hpos : Lt (number 0) p.val.left) (hgt : Lt (number 1) p.val.right) :
    Lt p p.val.left := by
  obtain ⟨z, a, hz, ha, hapos⟩ := hpos
  change M.number (0 : ℂ) = M.number (z : ℂ) at hz
  have hz0 : z = 0 := by exact_mod_cast (M.number_injective hz).symm
  subst z
  obtain ⟨one, b, h1, hb, hbgt⟩ := hgt
  change M.number (1 : ℂ) = M.number (one : ℂ) at h1
  have hone : one = 1 := by exact_mod_cast (M.number_injective h1).symm
  subst one
  refine ⟨a / b, a, ?_, ha, div_lt_self hapos hbgt⟩
  change M.divValue (denote p.val.left) (denote p.val.right) = _
  have hbn : (b : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hbgt))
  rw [ha, hb, M.div_numbers _ _ hbn, Complex.ofReal_div]

end Litex


namespace Litex

/-- Eliminate membership of the actual certified builder without rebuilding it. -/
theorem inSetBuilderObj_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (s : Obj (M := M) (SetBuilderObj (M := M) β)) :
    In a s ↔ ∃ ha : In a s.val.bound,
      s.val.predicate (semanticObject (denote a) (M.member_isSet ha)) ha := by
  change M.mem (denote a) (S.sepValue (denote s.val.bound) s.val.condition) ↔ _
  rw [S.sep_members]
  exact ⟨fun h => h.2, fun h => ⟨h.choose, h⟩⟩

end Litex

namespace Litex


inductive InfiniteLimitDirection where
  | positive | negative

def infiniteBeyond (direction : InfiniteLimitDirection) (bound input : ℝ) : Prop :=
  match direction with
  | .positive => bound < input
  | .negative => input < bound

def commonInfinityThreshold (direction : InfiniteLimitDirection) (a b : ℝ) : ℝ :=
  match direction with
  | .positive => Max.max a b
  | .negative => Min.min a b

theorem infiniteBeyond_common (direction : InfiniteLimitDirection) (a b input : ℝ)
    (h : infiniteBeyond direction (commonInfinityThreshold direction a b) input) :
    infiniteBeyond direction a input ∧ infiniteBeyond direction b input := by
  cases direction with
  | positive => exact ⟨lt_of_le_of_lt (le_max_left _ _) h, lt_of_le_of_lt (le_max_right _ _) h⟩
  | negative => exact ⟨lt_of_lt_of_le h (min_le_left _ _), lt_of_lt_of_le h (min_le_right _ _)⟩

def InfiniteFunctionAccumulationValue (M : Semantics.{u}) [FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f : M.Value) : Prop :=
  ∀ bound : ℝ, ∃ input : ℝ,
    M.mem (M.number (input : ℂ)) (FunctionSemantics.domainValue f) ∧
    infiniteBeyond direction bound input

def InfiniteFunctionEpsilonValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f : M.Value) (value : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ bound : ℝ,
    ∀ input : ℝ, M.mem (M.number (input : ℂ)) (F.domainValue f) →
      infiniteBeyond direction bound input →
      ∃ output : ℝ, F.callValue f (M.number (input : ℂ)) = M.number (output : ℂ) ∧
        |output - value| < epsilon

def HasInfiniteFunctionLimitValue (M : Semantics.{u}) [FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f value : M.Value) : Prop :=
  ∃ l : ℝ, value = M.number (l : ℂ) ∧
    InfiniteFunctionAccumulationValue M direction f ∧ InfiniteFunctionEpsilonValue M direction f l

def HasInfiniteFunctionLimit {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α) (value : Obj (M := M) β) : Prop :=
  HasInfiniteFunctionLimitValue M direction (denote f) (denote value)

theorem infiniteFunctionLimitUnique {M : Semantics.{u}} [F : FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f : M.Value) (r s : ℝ)
    (ha : InfiniteFunctionAccumulationValue M direction f)
    (hr : InfiniteFunctionEpsilonValue M direction f r)
    (hs : InfiniteFunctionEpsilonValue M direction f s) : r = s := by
  by_contra hne
  have hdist : 0 < |r-s| := abs_pos.mpr (sub_ne_zero.mpr hne)
  let epsilon := |r-s| / 2
  have he : 0 < epsilon := by dsimp [epsilon]; linarith
  obtain ⟨a, h1⟩ := hr epsilon he
  obtain ⟨b, h2⟩ := hs epsilon he
  obtain ⟨input, hinput, hbeyond⟩ := ha (commonInfinityThreshold direction a b)
  obtain ⟨hleft, hright⟩ := infiniteBeyond_common direction a b input hbeyond
  obtain ⟨u, hu, hur⟩ := h1 input hinput hleft
  obtain ⟨v, hv, hvs⟩ := h2 input hinput hright
  have huv : u = v := Complex.ofReal_injective (M.number_injective (hu.symm.trans hv))
  subst v
  have htriangle := abs_sub_le r u s
  rw [abs_sub_comm r u] at htriangle
  dsimp [epsilon] at hur hvs
  linarith

theorem infiniteFunctionLimitCandidatesEqual {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α)
    (a : Obj (M := M) β) (b : Obj (M := M) γ)
    (ha : HasInfiniteFunctionLimit direction f a) (hb : HasInfiniteFunctionLimit direction f b) :
    Same a b := by
  obtain ⟨r, hr, hacc, her⟩ := ha
  obtain ⟨s, hs, _, hes⟩ := hb
  have hrs := infiniteFunctionLimitUnique direction (denote f) r s hacc her hes
  exact hr.trans ((congrArg (fun z : ℝ => M.number (z : ℂ)) hrs).trans hs.symm)

def InfiniteFunctionConvergentValue (M : Semantics.{u}) [FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f : M.Value) : Prop :=
  ∃ value : ℝ, HasInfiniteFunctionLimitValue M direction f (M.number (value : ℂ))

noncomputable def infiniteFunctionLimitValue {M : Semantics.{u}} [FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f : M.Value) : M.Value := by
  classical
  let selected : ℝ := if h : InfiniteFunctionConvergentValue M direction f
    then Classical.choose h else 0
  exact M.number (selected : ℂ)

structure InfiniteFunctionLimitObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  function : Obj (M := M) α
  direction : InfiniteLimitDirection

noncomputable instance infiniteFunctionLimitRepresentation {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] :
    Representation M (InfiniteFunctionLimitObj (M := M) α) where
  wd p := RealFunctionValue M (denote p.function) ∧
    InfiniteFunctionConvergentValue M p.direction (denote p.function)
  denote p := infiniteFunctionLimitValue p.direction (denote p.function)
  wd_isSet {p} _ := by
    unfold infiniteFunctionLimitValue
    exact M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def infiniteFunctionLimit {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α)
    (hf : RealFunctionValue M (denote f))
    (hc : InfiniteFunctionConvergentValue M direction (denote f)) :
    Obj (M := M) (InfiniteFunctionLimitObj (M := M) α) := ⟨⟨f, direction⟩, hf, hc⟩

theorem infiniteFunctionConvergentOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α) (value : Obj (M := M) β)
    (h : HasInfiniteFunctionLimit direction f value) :
    InfiniteFunctionConvergentValue M direction (denote f) := by
  obtain ⟨l, hl, ha, he⟩ := h
  exact ⟨l, l, rfl, ha, he⟩

theorem infiniteFunctionConvergentOfExistence {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α)
    (h : ∃ value : Obj (M := M) M.Value, ∃ _ : In value R,
      HasInfiniteFunctionLimit direction f value) :
    InfiniteFunctionConvergentValue M direction (denote f) := by
  obtain ⟨value, _, h⟩ := h
  exact infiniteFunctionConvergentOfCandidate direction f value h

theorem infiniteFunctionLimitEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (InfiniteFunctionLimitObj (M := M) α)) (value : Obj (M := M) β)
    (h : HasInfiniteFunctionLimit p.val.direction p.val.function value) : Same p value := by
  classical
  have hc := p.wd.2
  have chosen := Classical.choose_spec hc
  have heq := infiniteFunctionLimitCandidatesEqual p.val.direction p.val.function
    (number (M := M) ((Classical.choose hc : ℝ) : ℂ)) value chosen h
  change infiniteFunctionLimitValue p.val.direction (denote p.val.function) = denote value
  unfold infiniteFunctionLimitValue
  rw [dif_pos hc]
  exact heq

theorem infiniteFunctionLimitInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (InfiniteFunctionLimitObj (M := M) α)) : In p R := by
  classical
  change M.mem (infiniteFunctionLimitValue p.val.direction (denote p.val.function)) _
  unfold infiniteFunctionLimitValue
  exact (M.real_members _).mpr ⟨_, rfl⟩

end Litex

namespace Litex


def infiniteBeyondValue (M : Semantics.{u}) (direction : InfiniteLimitDirection)
    (bound input : M.Value) : Prop :=
  match direction with
  | .positive => RealLtValue M bound input
  | .negative => RealLtValue M input bound

theorem infiniteBeyondValue_numbers {M : Semantics.{u}}
    (direction : InfiniteLimitDirection) (bound input : ℝ) :
    infiniteBeyondValue M direction (M.number (bound : ℂ)) (M.number (input : ℂ)) ↔
      infiniteBeyond direction bound input := by
  cases direction <;> exact realLtValue_numbers _ _

noncomputable def infiniteLimitTailValue {M : Semantics.{u}} [SetSemantics M]
    (direction : InfiniteLimitDirection) (domain bound : M.Value) : M.Value :=
  SetSemantics.sepValue domain (fun input => ∃ _ : M.mem input domain,
    infiniteBeyondValue M direction bound input)

def InfiniteLimitAccumulationClauseValue (M : Semantics.{u})
    (direction : InfiniteLimitDirection) (domain bound : M.Value) : Prop :=
  ∃ input : Obj (M := M) M.Value, ∃ _ : M.mem (denote input) domain,
    infiniteBeyondValue M direction bound (denote input)

def InfiniteLimitEpsilonClauseValue (M : Semantics.{u}) [FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f domain value epsilon : M.Value) : Prop :=
  ∃ bound : Obj (M := M) M.Value, ∃ _ : In bound R,
    ∀ input, M.mem input (infiniteLimitTailValue direction domain (denote bound)) →
      M.mem input (FunctionSemantics.preimageValue f
        (fun y => M.mem y (sequenceEpsilonBallValue value epsilon)))

theorem infiniteFunctionLimitOfForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α)
    (value : Obj (M := M) β) (domain : Obj (M := M) γ)
    (hf : RealFunctionValue M (denote f))
    (hD : denote domain = F.domainValue (denote f))
    (hv : In value R)
    (ha : ∀ {σ : Type y} [Representation M σ], (bound : Obj (M := M) σ) →
      In bound R → InfiniteLimitAccumulationClauseValue M direction (denote domain) (denote bound))
    (he : ∀ {σ : Type z} [Representation M σ], (epsilon : Obj (M := M) σ) →
      In epsilon RPos → InfiniteLimitEpsilonClauseValue M direction (denote f) (denote domain) (denote value) (denote epsilon)) :
    HasInfiniteFunctionLimit direction f value := by
  let l := NativeBridge.asReal value hv
  have hlvalue : denote value = M.number (l : ℂ) := NativeBridge.asReal_spec value hv
  have ha := forallMembersOfRepresentations R ha
  have he := forallMembersOfRepresentations RPos he
  obtain ⟨signature, hfn, hinput, _⟩ := hf
  have hdomain : denote domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  refine ⟨l, hlvalue, ?_, ?_⟩
  · intro bound
    obtain ⟨input, hmem, hbeyond⟩ := ha (M.number (bound : ℂ)) (NativeBridge.numberInR bound)
    obtain ⟨x, hx⟩ := (M.real_members (denote input)).mp (hinput _ (hdomain ▸ hmem))
    refine ⟨x, ?_, ?_⟩
    · rw [← hx, ← hD]
      exact hmem
    · rw [hx] at hbeyond
      exact (infiniteBeyondValue_numbers direction bound x).mp hbeyond
  · intro epsilon hepsilon
    obtain ⟨bound, hbound, hcontrol⟩ := he (M.number (epsilon : ℂ)) (numberInRPos epsilon hepsilon)
    let b := NativeBridge.asReal bound hbound
    have hbvalue : denote bound = M.number (b : ℂ) := NativeBridge.asReal_spec bound hbound
    refine ⟨b, ?_⟩
    intro x hx hbeyond
    have hxD : M.mem (M.number (x : ℂ)) (denote domain) := hD ▸ hx
    have htail : M.mem (M.number (x : ℂ))
        (infiniteLimitTailValue direction (denote domain) (denote bound)) := by
      apply (F.sep_members _ _ _).mpr
      refine ⟨hxD, hxD, ?_⟩
      rw [hbvalue]
      exact (infiniteBeyondValue_numbers direction b x).mpr hbeyond
    have image := ((F.preimage_mem_iff (fun y => M.mem y
      (sequenceEpsilonBallValue (denote value) (M.number (epsilon : ℂ))))
      signature.domain_isSet hfn).mp (hcontrol _ htail)).2
    obtain ⟨hyR, _, hless⟩ := (F.sep_members _ _ _).mp image
    obtain ⟨y, hy⟩ := (M.real_members _).mp hyR
    refine ⟨y, hy, ?_⟩
    change RealLtValue M (absValue (M.subValue
      (F.callValue (denote f) (M.number (x : ℂ))) (denote value))) (M.number (epsilon : ℂ)) at hless
    rw [hy, hlvalue, M.sub_numbers, ← Complex.ofReal_sub, absValue_number] at hless
    exact (realLtValue_numbers _ epsilon).mp hless

end Litex

namespace Litex


theorem finiteFunctionLimitExists {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (value : Obj (M := M) γ) (h : HasFiniteFunctionLimit side f point value) :
    ∃ witness : Obj (M := M) M.Value, ∃ _ : In witness R,
      HasFiniteFunctionLimit side f point witness := by
  obtain ⟨p, l, hp, _, ha, he⟩ := h
  have hreal : M.mem (M.number (l : ℂ)) (denote (R (M := M))) :=
    (M.real_members _).mpr ⟨l, rfl⟩
  let witness := semanticObject (M.number (l : ℂ)) (M.member_isSet hreal)
  exact ⟨witness, hreal, p, l, hp, rfl, ha, he⟩

theorem finiteFunctionLimitSelected {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteFunctionLimitObj (M := M) α β)) :
    HasFiniteFunctionLimit p.val.side p.val.function p.val.point p := by
  classical
  have hc := p.wd.2.2
  change HasFiniteFunctionLimitValue M p.val.side (denote p.val.function)
    (denote p.val.point) (finiteFunctionLimitValue p.val.side (denote p.val.function) (denote p.val.point))
  unfold finiteFunctionLimitValue
  rw [dif_pos hc]
  exact Classical.choose_spec hc

theorem infiniteFunctionLimitExists {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α)
    (value : Obj (M := M) β) (h : HasInfiniteFunctionLimit direction f value) :
    ∃ witness : Obj (M := M) M.Value, ∃ _ : In witness R,
      HasInfiniteFunctionLimit direction f witness := by
  obtain ⟨l, _, ha, he⟩ := h
  have hreal : M.mem (M.number (l : ℂ)) (denote (R (M := M))) :=
    (M.real_members _).mpr ⟨l, rfl⟩
  let witness := semanticObject (M.number (l : ℂ)) (M.member_isSet hreal)
  exact ⟨witness, hreal, l, rfl, ha, he⟩

theorem infiniteFunctionLimitSelected {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (InfiniteFunctionLimitObj (M := M) α)) :
    HasInfiniteFunctionLimit p.val.direction p.val.function p := by
  classical
  have hc := p.wd.2
  change HasInfiniteFunctionLimitValue M p.val.direction (denote p.val.function)
    (infiniteFunctionLimitValue p.val.direction (denote p.val.function))
  unfold infiniteFunctionLimitValue
  rw [dif_pos hc]
  exact Classical.choose_spec hc

end Litex

namespace Litex


theorem sequenceLimitSelected {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (SequenceLimitObj (M := M) α)) :
    HasSequenceLimit p.val.sequence p := by
  classical
  have hc := p.wd.2
  change HasSequenceLimitValue M (denote p.val.sequence) (sequenceLimitValue (denote p.val.sequence))
  unfold sequenceLimitValue
  rw [dif_pos hc]
  exact (Classical.choose_spec hc).2

theorem sequenceLimitTail {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (value : Obj (M := M) β) (epsilon : Obj (M := M) γ)
    (h : HasSequenceLimit a value) (hepsilon : In epsilon RPos) :
    ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
      SequenceLimitTailValue M (denote a) (denote value) (denote epsilon) (denote cutoff) :=
  h (denote epsilon) hepsilon

end Litex

namespace Litex


theorem sequenceEpsilonBall_self {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (value : Obj (M := M) α) (epsilon : Obj (M := M) β)
    (hv : In value R) (he : In epsilon RPos) :
    M.mem (denote value) (sequenceEpsilonBallValue (denote value) (denote epsilon)) := by
  apply (F.sep_members _ _ _).mpr
  refine ⟨hv, hv, ?_⟩
  change RealLtValue M (absValue (M.subValue (denote value) (denote value))) (denote epsilon)
  obtain ⟨r, hr⟩ := (M.real_members _).mp hv
  have hzero : absValue (M.subValue (denote value) (denote value)) = M.number 0 := by
    rw [hr, M.sub_numbers, sub_self, show (0 : ℂ) = ((0 : ℝ) : ℂ) by rfl,
      absValue_number, abs_zero]
  rw [hzero]
  exact inRPos_positive epsilon he

theorem finiteFunctionLimitConstant {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (value : Obj (M := M) γ) (domain : Obj (M := M) δ)
    (hf : RealFunctionValue M (denote f))
    (hD : denote domain = F.domainValue (denote f))
    (hp : In point R) (hv : In value R)
    (ha : ∀ {σ : Type z} [Representation M σ], (radius : Obj (M := M) σ) →
      In radius RPos → FiniteLimitAccumulationClauseValue M side (denote domain) (denote point) (denote radius))
    (hconstant : ∀ {σ : Type t} [Representation M σ], (input : Obj (M := M) σ) →
      In input domain → F.callValue (denote f) (denote input) = denote value) :
    HasFiniteFunctionLimit side f point value := by
  apply finiteFunctionLimitOfForall.{u,v,w,x,y,z,0} side f point value domain hf hD hp hv ha
  intro σ rep epsilon hepsilon
  have hone : M.mem (M.number (1 : ℂ)) (denote (RPos (M := M))) := numberInRPos 1 zero_lt_one
  let cutoff := semanticObject (M.number (1 : ℂ)) (M.member_isSet hone)
  refine ⟨cutoff, hone, ?_⟩
  intro input hneighborhood
  have hinput : M.mem input (denote domain) := ((F.sep_members _ _ _).mp hneighborhood).1
  have image := forallMembersOfRepresentations (P := fun x => F.callValue (denote f) x = denote value) domain (fun {_} [_] x hx => hconstant x hx) input hinput
  obtain ⟨signature, hfn, _, _⟩ := hf
  have hd : denote domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  apply (F.preimage_mem_iff _ signature.domain_isSet hfn).mpr
  refine ⟨hd ▸ hinput, ?_⟩
  rw [image]
  exact sequenceEpsilonBall_self value epsilon hv hepsilon

theorem infiniteFunctionLimitConstant {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α)
    (value : Obj (M := M) β) (domain : Obj (M := M) γ)
    (hf : RealFunctionValue M (denote f))
    (hD : denote domain = F.domainValue (denote f))
    (hv : In value R)
    (ha : ∀ {σ : Type y} [Representation M σ], (bound : Obj (M := M) σ) →
      In bound R → InfiniteLimitAccumulationClauseValue M direction (denote domain) (denote bound))
    (hconstant : ∀ {σ : Type z} [Representation M σ], (input : Obj (M := M) σ) →
      In input domain → F.callValue (denote f) (denote input) = denote value) :
    HasInfiniteFunctionLimit direction f value := by
  apply infiniteFunctionLimitOfForall.{u,v,w,x,y,0} direction f value domain hf hD hv ha
  intro σ rep epsilon hepsilon
  have hzero : M.mem (M.number (0 : ℂ)) (denote (R (M := M))) := NativeBridge.numberInR 0
  let cutoff := semanticObject (M.number (0 : ℂ)) (M.member_isSet hzero)
  refine ⟨cutoff, hzero, ?_⟩
  intro input htail
  have hinput : M.mem input (denote domain) := ((F.sep_members _ _ _).mp htail).1
  have image := forallMembersOfRepresentations (P := fun x => F.callValue (denote f) x = denote value) domain (fun {_} [_] x hx => hconstant x hx) input hinput
  obtain ⟨signature, hfn, _, _⟩ := hf
  have hd : denote domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  apply (F.preimage_mem_iff _ signature.domain_isSet hfn).mpr
  refine ⟨hd ▸ hinput, ?_⟩
  rw [image]
  exact sequenceEpsilonBall_self value epsilon hv hepsilon

end Litex

namespace Litex


theorem sequenceEpsilonBall_numbers {M : Semantics.{u}} [S : SetSemantics M]
    (value epsilon output : ℝ) :
    M.mem (M.number (output : ℂ))
      (sequenceEpsilonBallValue (M.number (value : ℂ)) (M.number (epsilon : ℂ))) ↔
      |output - value| < epsilon := by
  rw [sequenceEpsilonBallValue, S.sep_members]
  constructor
  · rintro ⟨_, _, h⟩
    change RealLtValue M (absValue (M.subValue (M.number (output : ℂ))
      (M.number (value : ℂ)))) (M.number (epsilon : ℂ)) at h
    rw [M.sub_numbers, ← Complex.ofReal_sub, absValue_number] at h
    exact (realLtValue_numbers _ epsilon).mp h
  · intro h
    have hreal : M.mem (M.number (output : ℂ)) (denote (R (M := M))) :=
      (M.real_members _).mpr ⟨output, rfl⟩
    refine ⟨hreal, hreal, ?_⟩
    change RealLtValue M (absValue (M.subValue (M.number (output : ℂ))
      (M.number (value : ℂ)))) (M.number (epsilon : ℂ))
    rw [M.sub_numbers, ← Complex.ofReal_sub, absValue_number]
    exact (realLtValue_numbers _ epsilon).mpr h

theorem finiteFunctionLimitAccumulation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y} {σ : Type z}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M σ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (value : Obj (M := M) γ) (domain : Obj (M := M) δ)
    (hD : denote domain = F.domainValue (denote f))
    (h : HasFiniteFunctionLimit side f point value)
    (radius : Obj (M := M) σ) (hradius : In radius RPos) :
    FiniteLimitAccumulationClauseValue M side (denote domain) (denote point) (denote radius) := by
  obtain ⟨p, _, hp, _, ha, _⟩ := h
  obtain ⟨r, hr, hrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
  obtain ⟨input, hinput, hpositive, hnear⟩ := ha r hrpos
  have hmem : M.mem (M.number (input : ℂ)) (denote domain) := hD ▸ hinput
  let witness := semanticObject (M.number (input : ℂ)) (M.member_isSet hmem)
  refine ⟨witness, hmem, ?_, ?_⟩
  · change RealLtValue M (M.number 0) (finiteLimitDistanceValue side (denote point) (M.number (input : ℂ)))
    rw [hp, finiteLimitDistanceValue_numbers]
    exact (realLtValue_numbers 0 _).mpr hpositive
  · change RealLtValue M (finiteLimitDistanceValue side (denote point) (M.number (input : ℂ))) (denote radius)
    rw [hp, hr, finiteLimitDistanceValue_numbers]
    exact (realLtValue_numbers _ r).mpr hnear

theorem finiteFunctionLimitControl {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y} {σ : Type z}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M σ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (value : Obj (M := M) γ) (domain : Obj (M := M) δ)
    (hf : RealFunctionValue M (denote f))
    (hD : denote domain = F.domainValue (denote f))
    (h : HasFiniteFunctionLimit side f point value)
    (epsilon : Obj (M := M) σ) (hepsilon : In epsilon RPos) :
    FiniteLimitEpsilonClauseValue M side (denote f) (denote domain) (denote point)
      (denote value) (denote epsilon) := by
  obtain ⟨p, l, hp, hl, _, he⟩ := h
  obtain ⟨e, hevalue, hepos⟩ := NativeBridge.realWitnessOfPositive epsilon (inRPos_positive epsilon hepsilon)
  obtain ⟨d, hd, hestimate⟩ := he e hepos
  have hdmem : M.mem (M.number (d : ℂ)) (denote (RPos (M := M))) := numberInRPos d hd
  let delta := semanticObject (M.number (d : ℂ)) (M.member_isSet hdmem)
  refine ⟨delta, hdmem, ?_⟩
  intro input hneighborhood
  obtain ⟨hxD, _, hpositive, hnear⟩ := (F.sep_members _ _ _).mp hneighborhood
  obtain ⟨signature, hfn, hreal, _⟩ := hf
  have hsignature : denote domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  obtain ⟨x, hx⟩ := (M.real_members input).mp (hreal input (hsignature ▸ hxD))
  have hxgraph : M.mem (M.number (x : ℂ)) (F.domainValue (denote f)) := by
    rw [← hx, ← hD]
    exact hxD
  change RealLtValue M (M.number 0) (finiteLimitDistanceValue side (denote point) input) at hpositive
  change RealLtValue M (finiteLimitDistanceValue side (denote point) input) (M.number (d : ℂ)) at hnear
  rw [hp, hx, finiteLimitDistanceValue_numbers] at hpositive hnear
  obtain ⟨output, houtput, hclose⟩ := hestimate x hxgraph
    ((realLtValue_numbers 0 _).mp hpositive) ((realLtValue_numbers _ d).mp hnear)
  apply (F.preimage_mem_iff _ signature.domain_isSet hfn).mpr
  refine ⟨hsignature ▸ hxD, ?_⟩
  rw [hx, houtput, hl, hevalue]
  exact (sequenceEpsilonBall_numbers l e output).mpr hclose

theorem infiniteFunctionLimitAccumulation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {σ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M σ]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α)
    (value : Obj (M := M) β) (domain : Obj (M := M) γ)
    (hD : denote domain = F.domainValue (denote f))
    (h : HasInfiniteFunctionLimit direction f value)
    (bound : Obj (M := M) σ) (hbound : In bound R) :
    InfiniteLimitAccumulationClauseValue M direction (denote domain) (denote bound) := by
  obtain ⟨_, _, ha, _⟩ := h
  obtain ⟨b, hb⟩ := (M.real_members _).mp hbound
  obtain ⟨input, hinput, hbeyond⟩ := ha b
  have hmem : M.mem (M.number (input : ℂ)) (denote domain) := hD ▸ hinput
  let witness := semanticObject (M.number (input : ℂ)) (M.member_isSet hmem)
  refine ⟨witness, hmem, ?_⟩
  change infiniteBeyondValue M direction (denote bound) (M.number (input : ℂ))
  rw [hb]
  exact (infiniteBeyondValue_numbers direction b input).mpr hbeyond

theorem infiniteFunctionLimitControl {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {σ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M σ]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α)
    (value : Obj (M := M) β) (domain : Obj (M := M) γ)
    (hf : RealFunctionValue M (denote f))
    (hD : denote domain = F.domainValue (denote f))
    (h : HasInfiniteFunctionLimit direction f value)
    (epsilon : Obj (M := M) σ) (hepsilon : In epsilon RPos) :
    InfiniteLimitEpsilonClauseValue M direction (denote f) (denote domain) (denote value) (denote epsilon) := by
  obtain ⟨l, hl, _, he⟩ := h
  obtain ⟨e, hevalue, hepos⟩ := NativeBridge.realWitnessOfPositive epsilon (inRPos_positive epsilon hepsilon)
  obtain ⟨b, hestimate⟩ := he e hepos
  have hbmem : M.mem (M.number (b : ℂ)) (denote (R (M := M))) := NativeBridge.numberInR b
  let bound := semanticObject (M.number (b : ℂ)) (M.member_isSet hbmem)
  refine ⟨bound, hbmem, ?_⟩
  intro input htail
  obtain ⟨hxD, _, hbeyond⟩ := (F.sep_members _ _ _).mp htail
  obtain ⟨signature, hfn, hreal, _⟩ := hf
  have hsignature : denote domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  obtain ⟨x, hx⟩ := (M.real_members input).mp (hreal input (hsignature ▸ hxD))
  have hxgraph : M.mem (M.number (x : ℂ)) (F.domainValue (denote f)) := by
    rw [← hx, ← hD]
    exact hxD
  change infiniteBeyondValue M direction (M.number (b : ℂ)) input at hbeyond
  rw [hx] at hbeyond
  obtain ⟨output, houtput, hclose⟩ := hestimate x hxgraph
    ((infiniteBeyondValue_numbers direction b x).mp hbeyond)
  apply (F.preimage_mem_iff _ signature.domain_isSet hfn).mpr
  refine ⟨hsignature ▸ hxD, ?_⟩
  rw [hx, houtput, hl, hevalue]
  exact (sequenceEpsilonBall_numbers l e output).mpr hclose

end Litex


namespace Litex

theorem realFiniteLimitAccumulation {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (side : FiniteLimitSide) (point : Obj (M := M) α) (hp : In point R)
    (radius : Obj (M := M) β) (hr : In radius RPos) :
    FiniteLimitAccumulationClauseValue M side (denote (R (M := M))) (denote point) (denote radius) := by
  obtain ⟨p, hp⟩ := (M.real_members _).mp hp
  obtain ⟨r, hr, hpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hr)
  let x : ℝ := match side with | .both => p+r/2 | .left => p-r/2 | .right => p+r/2
  have hdist : finiteLimitDistance side p x = r/2 := by
    cases side <;> dsimp [finiteLimitDistance, x]
    · rw [show p+r/2-p = r/2 by ring, abs_of_pos (by linarith)]
    · ring
    · ring
  have hmem : M.mem (M.number (x : ℂ)) (denote (R (M := M))) := NativeBridge.numberInR x
  refine ⟨semanticObject (M.number (x : ℂ)) (M.member_isSet hmem), hmem, ?_, ?_⟩
  · change RealLtValue M (M.number 0) (finiteLimitDistanceValue side (denote point) (M.number (x : ℂ)))
    rw [hp, finiteLimitDistanceValue_numbers, hdist]
    exact (realLtValue_numbers 0 (r/2)).mpr (by linarith)
  · change RealLtValue M (finiteLimitDistanceValue side (denote point) (M.number (x : ℂ))) (denote radius)
    rw [hp, hr, finiteLimitDistanceValue_numbers, hdist]
    exact (realLtValue_numbers (r/2) r).mpr (by linarith)

theorem realInfiniteLimitAccumulation {M : Semantics.{u}}
    {α : Type v} [Representation M α]
    (direction : InfiniteLimitDirection) (bound : Obj (M := M) α) (hb : In bound R) :
    InfiniteLimitAccumulationClauseValue M direction (denote (R (M := M))) (denote bound) := by
  obtain ⟨b, hb⟩ := (M.real_members _).mp hb
  let x : ℝ := match direction with | .positive => b+1 | .negative => b-1
  have hmem : M.mem (M.number (x : ℂ)) (denote (R (M := M))) := NativeBridge.numberInR x
  refine ⟨semanticObject (M.number (x : ℂ)) (M.member_isSet hmem), hmem, ?_⟩
  change infiniteBeyondValue M direction (denote bound) (M.number (x : ℂ))
  rw [hb]
  apply (infiniteBeyondValue_numbers direction b x).mpr
  cases direction <;> dsimp [infiniteBeyond, x] <;> linarith

theorem finiteLimitDistance_eq_abs (side : FiniteLimitSide) (point input : ℝ)
    (h : 0 < finiteLimitDistance side point input) :
    finiteLimitDistance side point input = |input-point| := by
  cases side with
  | both => rfl
  | left =>
      dsimp [finiteLimitDistance] at h ⊢
      rw [abs_of_neg (by linarith)]
      ring
  | right =>
      dsimp [finiteLimitDistance] at h ⊢
      rw [abs_of_pos h]

theorem finiteFunctionLimitIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (domain : Obj (M := M) γ) (hf : RealFunctionValue M (denote f))
    (hD : denote domain = F.domainValue (denote f)) (hp : In point R)
    (ha : ∀ {σ : Type y} [Representation M σ], (radius : Obj (M := M) σ) →
      In radius RPos → FiniteLimitAccumulationClauseValue M side (denote domain) (denote point) (denote radius))
    (hidentity : ∀ {σ : Type z} [Representation M σ], (input : Obj (M := M) σ) →
      In input domain → F.callValue (denote f) (denote input) = denote input) :
    HasFiniteFunctionLimit side f point point := by
  apply finiteFunctionLimitOfForall.{u,v,w,w,x,y,0} side f point point domain hf hD hp hp ha
  intro σ rep epsilon hepsilon
  refine ⟨semanticObject (denote epsilon) (isSet epsilon), hepsilon, ?_⟩
  intro input hneighborhood
  obtain ⟨hinput, _, hpositive, hnear⟩ := (F.sep_members _ _ _).mp hneighborhood
  have image := forallMembersOfRepresentations
    (P := fun x => F.callValue (denote f) x = x) domain (fun {_} [_] x hx => hidentity x hx) input hinput
  obtain ⟨signature, hfn, hreal, _⟩ := hf
  have hd : denote domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  obtain ⟨x, hx⟩ := (M.real_members input).mp (hreal _ (hd ▸ hinput))
  obtain ⟨p, hpvalue⟩ := (M.real_members _).mp hp
  obtain ⟨e, hevalue, _⟩ := NativeBridge.realWitnessOfPositive epsilon (inRPos_positive epsilon hepsilon)
  change RealLtValue M (M.number 0) (finiteLimitDistanceValue side (denote point) input) at hpositive
  change RealLtValue M (finiteLimitDistanceValue side (denote point) input) (denote epsilon) at hnear
  rw [hpvalue, hx, finiteLimitDistanceValue_numbers] at hpositive
  rw [hpvalue, hx, hevalue, finiteLimitDistanceValue_numbers] at hnear
  have hdistance := finiteLimitDistance_eq_abs side p x ((realLtValue_numbers 0 _).mp hpositive)
  have hestimate : |x-p| < e := by
    rw [← hdistance]
    exact (realLtValue_numbers _ e).mp hnear
  apply (F.preimage_mem_iff _ signature.domain_isSet hfn).mpr
  refine ⟨hd ▸ hinput, ?_⟩
  rw [image, hx, hpvalue, hevalue]
  exact (sequenceEpsilonBall_numbers p e x).mpr hestimate

end Litex


