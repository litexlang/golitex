import Litex.Matrices

universe u v w x r

namespace Litex

/-- A bound quantifies over source members. Real carriers are checked separately
by the source predicate's WD, so the empty set needs no nonempty premise. -/
def RealUpperBoundValue (M : Semantics.{u}) (A b : M.Value) : Prop :=
  ∀ x : M.Value, M.mem x A →
    ∃ r s : ℝ, x = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r ≤ s

def RealLowerBoundValue (M : Semantics.{u}) (A b : M.Value) : Prop :=
  ∀ x : M.Value, M.mem x A →
    ∃ r s : ℝ, b = M.number (r : ℂ) ∧ x = M.number (s : ℂ) ∧ r ≤ s

def RealUpperBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  RealUpperBoundValue M (denote A) (denote b)

def RealLowerBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  RealLowerBoundValue M (denote A) (denote b)

def RealBoundedAboveValue (M : Semantics.{u}) (A : M.Value) : Prop :=
  ∃ b : Obj (M := M) M.Value, ∃ _ : In b R, RealUpperBoundValue M A (denote b)

def RealBoundedAbove {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop := RealBoundedAboveValue M (denote A)

def RealBoundedBelowValue (M : Semantics.{u}) (A : M.Value) : Prop :=
  ∃ b : Obj (M := M) M.Value, ∃ _ : In b R, RealLowerBoundValue M A (denote b)

def RealBoundedBelow {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop := RealBoundedBelowValue M (denote A)

def RealBoundedValue (M : Semantics.{u}) (A : M.Value) : Prop :=
  RealBoundedBelowValue M A ∧ RealBoundedAboveValue M A

def RealBounded {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop := RealBoundedValue M (denote A)

theorem realUpperBoundOfForall {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (h : ∀ {γ : Type u} [Representation M γ], (x : Obj (M := M) γ) → In x A → Le x b) :
    RealUpperBound A b := fun x hx => h (semanticObject x (M.member_isSet hx)) hx

theorem realLowerBoundOfForall {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (h : ∀ {γ : Type u} [Representation M γ], (x : Obj (M := M) γ) → In x A → Le b x) :
    RealLowerBound A b := fun x hx => h (semanticObject x (M.member_isSet hx)) hx

end Litex

namespace Litex

/-- The ordinary real set observed from the source membership relation. -/
def realMemberSet (M : Semantics.{u}) (A : M.Value) : Set ℝ :=
  {r | M.mem (M.number (r : ℂ)) A}

theorem realUpperBound_iff_upperBounds {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) :
    RealUpperBound A b ↔ NativeBridge.asReal b hb ∈ upperBounds (realMemberSet M (denote A)) := by
  constructor
  · intro h r hr
    exact (NativeBridge.le_iff_ofDenoteReal (number (M := M) (r : ℂ)) b r
      (NativeBridge.asReal b hb) rfl (NativeBridge.asReal_spec b hb)).mp
      (h (M.number (r : ℂ)) hr)
  · intro h x hx
    obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
    exact ⟨r, NativeBridge.asReal b hb, hr, NativeBridge.asReal_spec b hb,
      h (by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx)⟩

theorem realLowerBound_iff_lowerBounds {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) :
    RealLowerBound A b ↔ NativeBridge.asReal b hb ∈ lowerBounds (realMemberSet M (denote A)) := by
  constructor
  · intro h r hr
    exact (NativeBridge.le_iff_ofDenoteReal b (number (M := M) (r : ℂ))
      (NativeBridge.asReal b hb) r (NativeBridge.asReal_spec b hb) rfl).mp
      (h (M.number (r : ℂ)) hr)
  · intro h x hx
    obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
    exact ⟨NativeBridge.asReal b hb, r, NativeBridge.asReal_spec b hb, hr,
      h (by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx)⟩

theorem realBoundedAbove_iff_bddAbove {M : Semantics.{u}} {α : Type v}
    [Representation M α] (A : Obj (M := M) α) (hA : Subset A R) :
    RealBoundedAbove A ↔ BddAbove (realMemberSet M (denote A)) := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨NativeBridge.asReal b hb, (realUpperBound_iff_upperBounds A b hA hb).mp h⟩
  · rintro ⟨b, hb⟩
    refine ⟨semanticObject (M.number (b : ℂ)) (isSet (number (M := M) (b : ℂ))), ?_, ?_⟩
    · exact (M.real_members _).mpr ⟨b, rfl⟩
    · intro x hx
      obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
      exact ⟨r,b,hr,rfl,hb (by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx)⟩

theorem realBoundedBelow_iff_bddBelow {M : Semantics.{u}} {α : Type v}
    [Representation M α] (A : Obj (M := M) α) (hA : Subset A R) :
    RealBoundedBelow A ↔ BddBelow (realMemberSet M (denote A)) := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨NativeBridge.asReal b hb, (realLowerBound_iff_lowerBounds A b hA hb).mp h⟩
  · rintro ⟨b, hb⟩
    refine ⟨semanticObject (M.number (b : ℂ)) (isSet (number (M := M) (b : ℂ))), ?_, ?_⟩
    · exact (M.real_members _).mpr ⟨b, rfl⟩
    · intro x hx
      obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
      exact ⟨b,r,rfl,hr,hb (by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx)⟩
end Litex

namespace Litex

/-- Nonemptiness observed through membership; no universal source set is used. -/
theorem realMemberSet_nonempty {M : Semantics.{u}} {α : Type v}
    [Representation M α] (A : Obj (M := M) α)
    (hA : Subset A R) (hne : IsNonempty A) :
    (realMemberSet M (denote A)).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
  exact ⟨r, by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx⟩

/-- The reserved source certificate includes a nonempty real carrier. -/
def RealLeastUpperBoundValue (M : Semantics.{u}) (A b : M.Value) : Prop :=
  (∀ x, M.mem x A → M.mem x (M.standard .real)) ∧
  (∃ x, M.mem x A) ∧ ∃ r : ℝ, b = M.number (r : ℂ) ∧ IsLUB (realMemberSet M A) r

def RealLeastUpperBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  RealLeastUpperBoundValue M (denote A) (denote b)

def RealSupremumExists {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop :=
  ∃ b : Obj (M := M) M.Value, ∃ _ : In b R, RealLeastUpperBound A b

noncomputable def supremumValue {M : Semantics.{u}} (A : M.Value) : M.Value :=
  M.number ((sSup (realMemberSet M A) : ℝ) : ℂ)

structure SupremumObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  set : Obj (M := M) α

noncomputable instance supremumRepresentation {M : Semantics.{u}}
    {α : Type v} [Representation M α] : Representation M (SupremumObj (M := M) α) where
  wd p := Subset p.set R ∧ RealSupremumExists p.set
  denote p := supremumValue (denote p.set)
  wd_isSet _ := M.member_isSet ((M.real_members _).mpr ⟨_,rfl⟩)

noncomputable def supremum {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (hA : Subset A R) (h : RealSupremumExists A) :
    Obj (M := M) (SupremumObj (M := M) α) := ⟨⟨A⟩,hA,h⟩

theorem supremumInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SupremumObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨_,rfl⟩

theorem realSupremumExistsOfCertificate {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (h : RealLeastUpperBound A b) :
    RealSupremumExists A := by
  refine ⟨semanticObject (denote b) (isSet b), ?_, h⟩
  obtain ⟨r,hr,_⟩ := h.2.2
  exact (M.real_members _).mpr ⟨r,hr⟩

theorem realSupremumExists {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (hA : Subset A R) (hne : IsNonempty A)
    (hb : RealBoundedAbove A) : RealSupremumExists A := by
  let r := sSup (realMemberSet M (denote A))
  refine ⟨semanticObject (M.number (r : ℂ)) (isSet (number (M := M) (r : ℂ))),
    (M.real_members _).mpr ⟨r,rfl⟩, hA, hne, r, rfl, ?_⟩
  exact isLUB_csSup (realMemberSet_nonempty A hA hne)
    ((realBoundedAbove_iff_bddAbove A hA).mp hb)

theorem supremumValue_eq_certificate {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (h : RealLeastUpperBound A b) :
    supremumValue (denote A) = denote b := by
  obtain ⟨r,hr,he⟩ := h.2.2
  rw [supremumValue, he.csSup_eq (realMemberSet_nonempty A h.1 h.2.1)]
  exact hr.symm

theorem supremumSelected {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SupremumObj (M := M) α)) : RealLeastUpperBound p.val.set p := by
  obtain ⟨b,_,hb⟩ := p.wd.2
  change RealLeastUpperBoundValue M (denote p.val.set) (supremumValue (denote p.val.set))
  rw [supremumValue_eq_certificate p.val.set b hb]
  exact hb

/-- The reserved source certificate includes a nonempty real carrier. -/
def RealGreatestLowerBoundValue (M : Semantics.{u}) (A b : M.Value) : Prop :=
  (∀ x, M.mem x A → M.mem x (M.standard .real)) ∧
  (∃ x, M.mem x A) ∧ ∃ r : ℝ, b = M.number (r : ℂ) ∧ IsGLB (realMemberSet M A) r

def RealGreatestLowerBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  RealGreatestLowerBoundValue M (denote A) (denote b)

def RealInfimumExists {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop :=
  ∃ b : Obj (M := M) M.Value, ∃ _ : In b R, RealGreatestLowerBound A b

noncomputable def infimumValue {M : Semantics.{u}} (A : M.Value) : M.Value :=
  M.number ((sInf (realMemberSet M A) : ℝ) : ℂ)

structure InfimumObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  set : Obj (M := M) α

noncomputable instance infimumRepresentation {M : Semantics.{u}}
    {α : Type v} [Representation M α] : Representation M (InfimumObj (M := M) α) where
  wd p := Subset p.set R ∧ RealInfimumExists p.set
  denote p := infimumValue (denote p.set)
  wd_isSet _ := M.member_isSet ((M.real_members _).mpr ⟨_,rfl⟩)

noncomputable def infimum {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (hA : Subset A R) (h : RealInfimumExists A) :
    Obj (M := M) (InfimumObj (M := M) α) := ⟨⟨A⟩,hA,h⟩

theorem infimumInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (InfimumObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨_,rfl⟩

theorem realInfimumExistsOfCertificate {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (h : RealGreatestLowerBound A b) :
    RealInfimumExists A := by
  refine ⟨semanticObject (denote b) (isSet b), ?_, h⟩
  obtain ⟨r,hr,_⟩ := h.2.2
  exact (M.real_members _).mpr ⟨r,hr⟩

theorem realInfimumExists {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (hA : Subset A R) (hne : IsNonempty A)
    (hb : RealBoundedBelow A) : RealInfimumExists A := by
  let r := sInf (realMemberSet M (denote A))
  refine ⟨semanticObject (M.number (r : ℂ)) (isSet (number (M := M) (r : ℂ))),
    (M.real_members _).mpr ⟨r,rfl⟩, hA, hne, r, rfl, ?_⟩
  exact isGLB_csInf (realMemberSet_nonempty A hA hne)
    ((realBoundedBelow_iff_bddBelow A hA).mp hb)

theorem infimumValue_eq_certificate {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (h : RealGreatestLowerBound A b) :
    infimumValue (denote A) = denote b := by
  obtain ⟨r,hr,he⟩ := h.2.2
  rw [infimumValue, he.csInf_eq (realMemberSet_nonempty A h.1 h.2.1)]
  exact hr.symm

theorem infimumSelected {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (InfimumObj (M := M) α)) : RealGreatestLowerBound p.val.set p := by
  obtain ⟨b,_,hb⟩ := p.wd.2
  change RealGreatestLowerBoundValue M (denote p.val.set) (infimumValue (denote p.val.set))
  rw [infimumValue_eq_certificate p.val.set b hb]
  exact hb

end Litex

-- Explicit extremal-certificate releases, preserving their source premises.
namespace Litex

theorem realLeastUpperBoundFromDefinition {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) (hne : IsNonempty A)
    (hbound : (∀ {γ : Type u} [Representation M γ], (z : Obj (M := M) γ) → In z A → Le z b))
    (hext : ∀ {γ : Type u} [Representation M γ], (c : Obj (M := M) γ) → In c R →
      RealUpperBound A c → Le b c) : RealLeastUpperBound A b := by
  refine ⟨hA, hne, NativeBridge.asReal b hb, NativeBridge.asReal_spec b hb, ?_, ?_⟩
  · exact (realUpperBound_iff_upperBounds A b hA hb).mp
      (realUpperBoundOfForall A b hbound)
  · intro r hr
    let c := semanticObject (M.number (r : ℂ)) (isSet (number (M := M) (r : ℂ)))
    have hc : In c R := (M.real_members _).mpr ⟨r,rfl⟩
    have hcval : NativeBridge.asReal c hc = r := by
      have h := NativeBridge.asReal_spec c hc
      change M.number (r : ℂ) = M.number ((NativeBridge.asReal c hc : ℝ) : ℂ) at h
      have h' := M.number_injective h
      exact_mod_cast h'.symm
    have bound : RealUpperBound A c := (realUpperBound_iff_upperBounds A c hA hc).mpr (hcval.symm ▸ hr)
    have h := hext c hc bound
    exact (NativeBridge.le_iff_ofDenoteReal b c (NativeBridge.asReal b hb) r (NativeBridge.asReal_spec b hb) rfl).mp h

theorem realLeastUpperBoundUpperBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (_hb : In b R) (h : RealLeastUpperBound A b) : RealUpperBound A b := by
  obtain ⟨r,hr,he⟩ := h.2.2
  intro z hz
  obtain ⟨s,hs⟩ := (M.real_members z).mp (hA z hz)
  exact ⟨s,r,hs,hr, he.1 (by change M.mem (M.number (s : ℂ)) (denote A); rw [← hs]; exact hz)⟩

theorem realLeastUpperBoundExists {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) (hne : IsNonempty A)
    (hbound : (∀ {γ : Type u} [Representation M γ], (z : Obj (M := M) γ) → In z A → Le z b)) : RealSupremumExists A :=
  realSupremumExists A hA hne
    ⟨semanticObject (denote b) (isSet b), hb, realUpperBoundOfForall A b hbound⟩

theorem realLeastUpperBoundUnique {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (_hA : Subset A R) (_hb : In b R) (hbcert : RealLeastUpperBound A b)
    (_hc : In c R) (hccert : RealLeastUpperBound A c) : Same b c :=
  (supremumValue_eq_certificate A b hbcert).symm.trans
    (supremumValue_eq_certificate A c hccert)

theorem realLeastUpperBoundMember {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (hb : In b R) (hcert : RealLeastUpperBound A b)
    (hc : In c A) : Le c b :=
  realLeastUpperBoundUpperBound A b hA hb hcert (denote c) hc

theorem realLeastUpperBoundCompareBound {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (_hb : In b R) (hcert : RealLeastUpperBound A b)
    (hc : In c R) (hbound : (∀ {δ : Type u} [Representation M δ], (z : Obj (M := M) δ) → In z A → Le z c)) : Le b c := by
  obtain ⟨r,hr,he⟩ := hcert.2.2
  have bound := (realUpperBound_iff_upperBounds A c hA hc).mp
    (realUpperBoundOfForall A c hbound)
  exact ⟨r,NativeBridge.asReal c hc,hr,NativeBridge.asReal_spec c hc,he.2 bound⟩

theorem realLeastUpperBoundCrosses {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (_hb : In b R) (hcert : RealLeastUpperBound A b)
    (hc : In c R) (hlt : Lt c b) :
    ∃ z : Obj (M := M) M.Value, ∃ _ : In z A, Lt c z := by
  obtain ⟨r,hr,he⟩ := hcert.2.2
  have cmp := (NativeBridge.lt_iff_ofDenoteReal c b (NativeBridge.asReal c hc) r (NativeBridge.asReal_spec c hc) hr).mp hlt
  have hne := realMemberSet_nonempty A hA hcert.2.1
  rw [← he.csSup_eq hne] at cmp
  obtain ⟨s,hs,hslt⟩ := exists_lt_of_lt_csSup hne cmp
  refine ⟨semanticObject (M.number (s : ℂ)) (isSet (number (M := M) (s : ℂ))), hs, ?_⟩
  exact ⟨NativeBridge.asReal c hc,s,NativeBridge.asReal_spec c hc,rfl,hslt⟩

theorem realGreatestLowerBoundFromDefinition {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) (hne : IsNonempty A)
    (hbound : (∀ {γ : Type u} [Representation M γ], (z : Obj (M := M) γ) → In z A → Le b z))
    (hext : ∀ {γ : Type u} [Representation M γ], (c : Obj (M := M) γ) → In c R →
      RealLowerBound A c → Le c b) : RealGreatestLowerBound A b := by
  refine ⟨hA, hne, NativeBridge.asReal b hb, NativeBridge.asReal_spec b hb, ?_, ?_⟩
  · exact (realLowerBound_iff_lowerBounds A b hA hb).mp
      (realLowerBoundOfForall A b hbound)
  · intro r hr
    let c := semanticObject (M.number (r : ℂ)) (isSet (number (M := M) (r : ℂ)))
    have hc : In c R := (M.real_members _).mpr ⟨r,rfl⟩
    have hcval : NativeBridge.asReal c hc = r := by
      have h := NativeBridge.asReal_spec c hc
      change M.number (r : ℂ) = M.number ((NativeBridge.asReal c hc : ℝ) : ℂ) at h
      have h' := M.number_injective h
      exact_mod_cast h'.symm
    have bound : RealLowerBound A c := (realLowerBound_iff_lowerBounds A c hA hc).mpr (hcval.symm ▸ hr)
    have h := hext c hc bound
    exact (NativeBridge.le_iff_ofDenoteReal c b r (NativeBridge.asReal b hb) rfl (NativeBridge.asReal_spec b hb)).mp h

theorem realGreatestLowerBoundLowerBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (_hb : In b R) (h : RealGreatestLowerBound A b) : RealLowerBound A b := by
  obtain ⟨r,hr,he⟩ := h.2.2
  intro z hz
  obtain ⟨s,hs⟩ := (M.real_members z).mp (hA z hz)
  exact ⟨r,s,hr,hs, he.1 (by change M.mem (M.number (s : ℂ)) (denote A); rw [← hs]; exact hz)⟩

theorem realGreatestLowerBoundExists {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) (hne : IsNonempty A)
    (hbound : (∀ {γ : Type u} [Representation M γ], (z : Obj (M := M) γ) → In z A → Le b z)) : RealInfimumExists A :=
  realInfimumExists A hA hne
    ⟨semanticObject (denote b) (isSet b), hb, realLowerBoundOfForall A b hbound⟩

theorem realGreatestLowerBoundUnique {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (_hA : Subset A R) (_hb : In b R) (hbcert : RealGreatestLowerBound A b)
    (_hc : In c R) (hccert : RealGreatestLowerBound A c) : Same b c :=
  (infimumValue_eq_certificate A b hbcert).symm.trans
    (infimumValue_eq_certificate A c hccert)

theorem realGreatestLowerBoundMember {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (hb : In b R) (hcert : RealGreatestLowerBound A b)
    (hc : In c A) : Le b c :=
  realGreatestLowerBoundLowerBound A b hA hb hcert (denote c) hc

theorem realGreatestLowerBoundCompareBound {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (_hb : In b R) (hcert : RealGreatestLowerBound A b)
    (hc : In c R) (hbound : (∀ {δ : Type u} [Representation M δ], (z : Obj (M := M) δ) → In z A → Le c z)) : Le c b := by
  obtain ⟨r,hr,he⟩ := hcert.2.2
  have bound := (realLowerBound_iff_lowerBounds A c hA hc).mp
    (realLowerBoundOfForall A c hbound)
  exact ⟨NativeBridge.asReal c hc,r,NativeBridge.asReal_spec c hc,hr,he.2 bound⟩

theorem realGreatestLowerBoundCrosses {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (_hb : In b R) (hcert : RealGreatestLowerBound A b)
    (hc : In c R) (hlt : Lt b c) :
    ∃ z : Obj (M := M) M.Value, ∃ _ : In z A, Lt z c := by
  obtain ⟨r,hr,he⟩ := hcert.2.2
  have cmp := (NativeBridge.lt_iff_ofDenoteReal b c r (NativeBridge.asReal c hc) hr (NativeBridge.asReal_spec c hc)).mp hlt
  have hne := realMemberSet_nonempty A hA hcert.2.1
  rw [← he.csInf_eq hne] at cmp
  obtain ⟨s,hs,hslt⟩ := exists_lt_of_csInf_lt hne cmp
  refine ⟨semanticObject (M.number (s : ℂ)) (isSet (number (M := M) (s : ℂ))), hs, ?_⟩
  exact ⟨s,NativeBridge.asReal c hc,rfl,NativeBridge.asReal_spec c hc,hslt⟩
end Litex

-- Sequence monotonicity and boundedness, retaining positive-natural indexing.
