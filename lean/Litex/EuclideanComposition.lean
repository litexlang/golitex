import Litex.MultivariableContinuity

namespace Litex
universe u

private theorem unaryContinuityControl {M : Semantics.{u}} [F : FunctionSemantics M]
    (g target : M.Value) (hg : RealFunctionValue M g)
    (hc : FunctionContinuousAtValue M .both g target) :
    ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
      ∃ delta : Obj (M := M) M.Value, In delta RPos ∧
        ∀ input, M.mem input (F.domainValue g) →
          RealLtValue M (absValue (M.subValue input target)) (denote delta) →
          RealLtValue M (absValue (M.subValue (F.callValue g input) (F.callValue g target))) epsilon := by
  obtain ⟨signature,hfn,_,_⟩ := hg
  intro epsilon he
  obtain ⟨delta,hd,hcontrol⟩ := hc epsilon he
  refine ⟨delta,hd,?_⟩
  intro input hi hclose
  have near : M.mem input (continuityNeighborhoodValue .both (F.domainValue g) target (denote delta)) :=
    (F.sep_members _ _ _).mpr ⟨hi,hi,hclose⟩
  have image := ((F.preimage_mem_iff _ signature.domain_isSet hfn).mp (hcontrol input near)).2
  obtain ⟨_,_,r,s,hr,hs,hbound⟩ := (F.sep_members _ _ _).mp image
  exact ⟨r,s,hr,hs,hbound⟩

/-- The exact common input domain and all-domain composition equation are retained. -/
theorem scalarMultivariableContinuityCompose {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n : M.Value) (hg : RealFunctionValue M g)
    (hD : F.domainValue h=F.domainValue f) (hp : M.mem point (F.domainValue f))
    (hmaps : ∀ x, M.mem x (F.domainValue f) → M.mem (F.callValue f x) (F.domainValue g))
    (hformula : ∀ x, M.mem x (F.domainValue f) → F.callValue h x=F.callValue g (F.callValue f x))
    (hcf : ScalarMultivariableContinuousAtValue M f point n)
    (hcg : FunctionContinuousAtValue M .both g (F.callValue f point)) :
    ScalarMultivariableContinuousAtValue M h point n := by
  intro epsilon he
  obtain ⟨outer,ho,control⟩ := unaryContinuityControl g (F.callValue f point) hg hcg epsilon he
  obtain ⟨delta,hd,inner⟩ := hcf (denote outer) ho
  refine ⟨delta,hd,?_⟩
  intro input hi hclose
  have hi : M.mem input (F.domainValue f) := hD ▸ hi
  rw [hformula input hi,hformula point hp]
  exact control (F.callValue f input) (hmaps input hi) (inner input hi hclose)

/-- Outer continuity is unpunctured, so inner values may equal their limit. -/
theorem scalarMultivariableLimitCompose {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n value : M.Value) (hg : RealFunctionValue M g)
    (hD : F.domainValue h=F.domainValue f)
    (hv : M.mem (F.callValue g value) (M.standard .real))
    (hmaps : ∀ x, M.mem x (F.domainValue f) → M.mem (F.callValue f x) (F.domainValue g))
    (hformula : ∀ x, M.mem x (F.domainValue f) → F.callValue h x=F.callValue g (F.callValue f x))
    (hl : HasMultivariableScalarLimitValue M f point n value)
    (hc : FunctionContinuousAtValue M .both g value) :
    HasMultivariableScalarLimitValue M h point n (F.callValue g value) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp hv
  obtain ⟨_,_,ha,he⟩ := hl
  refine ⟨r,hr,hD.symm ▸ ha,?_⟩
  intro epsilon hepsilon
  obtain ⟨outer,ho,control⟩ := unaryContinuityControl g value hg hc epsilon hepsilon
  obtain ⟨delta,hd,inner⟩ := he (denote outer) ho
  refine ⟨delta,hd,?_⟩
  intro input hi hpos hclose
  have hi : M.mem input (F.domainValue f) := hD ▸ hi
  rw [hformula input hi]
  exact control (F.callValue f input) (hmaps input hi) (inner input hi hpos hclose)

/-- Three independent dimensions are kept when composing vector continuity. -/
theorem vectorMultivariableContinuityCompose {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m k : M.Value)
    (hD : F.domainValue h=F.domainValue f) (hp : M.mem point (F.domainValue f))
    (hmaps : ∀ x, M.mem x (F.domainValue f) → M.mem (F.callValue f x) (F.domainValue g))
    (hformula : ∀ x, M.mem x (F.domainValue f) → F.callValue h x=F.callValue g (F.callValue f x))
    (hcf : VectorMultivariableContinuousAtValue M f point n m)
    (hcg : VectorMultivariableContinuousAtValue M g (F.callValue f point) m k) :
    VectorMultivariableContinuousAtValue M h point n k := by
  intro epsilon he
  obtain ⟨outer,ho,control⟩ := hcg epsilon he
  obtain ⟨delta,hd,inner⟩ := hcf (denote outer) ho
  refine ⟨delta,hd,?_⟩
  intro input hi hclose
  have hi : M.mem input (F.domainValue f) := hD ▸ hi
  rw [hformula input hi,hformula point hp]
  exact control (F.callValue f input) (hmaps input hi) (inner input hi hclose)

/-- The original accumulation clause is transported by equality of complete domains. -/
theorem vectorMultivariableLimitCompose {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m k value : M.Value)
    (hD : F.domainValue h=F.domainValue f)
    (hv : M.mem (F.callValue g value) (realVectorSetValue k))
    (hmaps : ∀ x, M.mem x (F.domainValue f) → M.mem (F.callValue f x) (F.domainValue g))
    (hformula : ∀ x, M.mem x (F.domainValue f) → F.callValue h x=F.callValue g (F.callValue f x))
    (hl : HasMultivariableVectorLimitValue M f point n m value)
    (hc : VectorMultivariableContinuousAtValue M g value m k) :
    HasMultivariableVectorLimitValue M h point n k (F.callValue g value) := by
  refine ⟨hv,hD.symm ▸ hl.2.1,?_⟩
  intro epsilon he
  obtain ⟨outer,ho,control⟩ := hc epsilon he
  obtain ⟨delta,hd,inner⟩ := hl.2.2 (denote outer) ho
  refine ⟨delta,hd,?_⟩
  intro input hi hpos hclose
  have hi : M.mem input (F.domainValue f) := hD ▸ hi
  rw [hformula input hi]
  exact control (F.callValue f input) (hmaps input hi) (inner input hi hpos hclose)

end Litex
