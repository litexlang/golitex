import Litex.UniformContinuity
universe u v w x y
namespace Litex

def FunctionLipschitzEstimateValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f constant pair : M.Value) : Prop :=
  RealLeValue M
    (absValue (M.subValue (F.callValue f (F.callValue pair (M.number 1)))
      (F.callValue f (F.callValue pair (M.number 2)))))
    (M.mulValue constant (absValue (M.subValue (F.callValue pair (M.number 1))
      (F.callValue pair (M.number 2)))))

def FunctionLipschitzValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f constant : M.Value) : Prop :=
  ∀ pair, M.mem pair (FiniteFunction.cartValue ![F.domainValue f, F.domainValue f]) →
    FunctionLipschitzEstimateValue M f constant pair

def FunctionLipschitz {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (constant : Obj (M := M) β) : Prop :=
  FunctionLipschitzValue M (denote f) (denote constant)

theorem functionLipschitzOfForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M δ]
    (f : Obj (M := M) α) (constant : Obj (M := M) β)
    (domain : Obj (M := M) δ) (hd : denote domain = F.domainValue (denote f))
    (h : ∀ {γ : Type x} [Representation M γ], (pair : Obj (M := M) γ) →
      M.mem (denote pair) (FiniteFunction.cartValue ![denote domain, denote domain]) →
        FunctionLipschitzEstimateValue M (denote f) (denote constant) (denote pair)) :
    FunctionLipschitz f constant := by
  intro pair hp
  let p := objectAtLevel.{u,x} pair (M.member_isSet hp)
  apply h p
  change M.mem pair (FiniteFunction.cartValue ![denote domain, denote domain])
  rw [hd]
  exact hp

theorem functionLipschitzForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M δ]
    (f : Obj (M := M) α) (constant : Obj (M := M) β)
    (domain : Obj (M := M) δ) (hd : denote domain = F.domainValue (denote f))
    (h : FunctionLipschitz f constant) :
    ∀ {γ : Type x} [Representation M γ], (pair : Obj (M := M) γ) →
      M.mem (denote pair) (FiniteFunction.cartValue ![denote domain, denote domain]) →
        FunctionLipschitzEstimateValue M (denote f) (denote constant) (denote pair) := by
  intro _ _ pair hp
  rw [hd] at hp
  exact h (denote pair) hp

theorem functionLipschitzUniform {M : Semantics.{u}} [F : FunctionSemantics M]
    (f constant : M.Value) (hk : RealLeValue M (M.number 0) constant)
    (h : FunctionLipschitzValue M f constant) : FunctionUniformContinuousValue M f := by
  obtain ⟨zero, k, hzero, hK, hkpos⟩ := hk
  have hz : zero = 0 := Complex.ofReal_injective (M.number_injective hzero).symm
  have hkpos : 0 ≤ k := hz ▸ hkpos
  intro epsilon hepsilon
  let eObj := semanticObject epsilon (M.member_isSet hepsilon)
  obtain ⟨e, he, hepos⟩ := NativeBridge.realWitnessOfPositive eObj (inRPos_positive eObj hepsilon)
  let d := e/(k+1)
  have hd : 0 < d := div_pos hepos (by linarith)
  have hdmem := numberInRPos (M := M) d hd
  let delta := semanticObject (M.number (d : ℂ)) (M.member_isSet hdmem)
  refine ⟨delta, hdmem, ?_⟩
  intro pair hnear
  obtain ⟨hpair, _, near⟩ := (F.sep_members _ _ _).mp hnear
  change RealLtValue M (absValue (M.subValue (F.callValue pair (M.number 1))
    (F.callValue pair (M.number 2)))) (M.number (d : ℂ)) at near
  obtain ⟨t, s, ht, hs, hts⟩ := near
  have hsd : s=d := Complex.ofReal_injective (M.number_injective hs).symm
  have htlt : t < d := hsd ▸ hts
  have estimate := h pair hpair
  change RealLeValue M _ _ at estimate
  change constant = M.number (k : ℂ) at hK
  rw [hK, ht, M.mul_numbers, ← Complex.ofReal_mul] at estimate
  obtain ⟨b, c, hb, hc, hbc⟩ := estimate
  have hcb : c=k*t := Complex.ofReal_injective (M.number_injective hc).symm
  have hbound : b ≤ k*t := hcb ▸ hbc
  have hproduct : (k+1)*d=e := by
    dsimp [d]
    field_simp
  have hkd : k*t ≤ k*d := mul_le_mul_of_nonneg_left (le_of_lt htlt) hkpos
  have hbe : b < e := by nlinarith
  apply (F.sep_members _ _ _).mpr
  refine ⟨hpair, hpair, ?_⟩
  exact ⟨b,e,hb,he,hbe⟩

end Litex
