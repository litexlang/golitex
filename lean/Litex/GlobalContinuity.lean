import Litex.Analysis

universe u v w x

namespace Litex

def FunctionContinuousValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f : M.Value) : Prop :=
  ∀ point, M.mem point (F.domainValue f) → FunctionContinuousAtValue M .both f point

def FunctionContinuous {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (f : Obj (M := M) α) : Prop :=
  FunctionContinuousValue M (denote f)

theorem functionContinuousOfForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (domain : Obj (M := M) β)
    (hd : denote domain = F.domainValue (denote f))
    (h : ∀ {γ : Type x} [Representation M γ], (point : Obj (M := M) γ) →
      In point domain → FunctionContinuousAt .both f point) : FunctionContinuous f := by
  intro point hp
  let p := objectAtLevel.{u,x} point (M.member_isSet hp)
  have hpD : In p domain := by
    change M.mem point (denote domain)
    rw [hd]
    exact hp
  exact h p hpD

theorem functionContinuousForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (domain : Obj (M := M) β)
    (hd : denote domain = F.domainValue (denote f)) (h : FunctionContinuous f) :
    ∀ {γ : Type x} [Representation M γ], (point : Obj (M := M) γ) →
      In point domain → FunctionContinuousAt .both f point := by
  intro _ _ point hp
  exact h (denote point) (hd ▸ hp)

theorem functionContinuousAtPoint {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point : M.Value) (h : FunctionContinuousValue M f)
    (hp : M.mem point (F.domainValue f)) : FunctionContinuousAtValue M .both f point :=
  h point hp

theorem functionContinuousOfConstant {M : Semantics.{u}} [F : FunctionSemantics M]
    (f value : M.Value) (hf : RealFunctionValue M f)
    (hv : M.mem value (M.standard .real))
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = value) :
    FunctionContinuousValue M f := by
  intro point hp
  exact functionContinuousAtOfConstant .both f point value hf hp hv formula

theorem functionContinuousOfIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = x) :
    FunctionContinuousValue M f := by
  intro point hp
  exact functionContinuousAtOfIdentity .both f point hf hp formula


end Litex

namespace Litex

theorem functionContinuousAtRestrictSide {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f point : M.Value) (hf : RealFunctionValue M f)
    (hp : M.mem point (F.domainValue f)) (h : FunctionContinuousAtValue M .both f point) :
    FunctionContinuousAtValue M side f point := by
  have hfc := hf
  obtain ⟨signature,hfn,inputReal,_⟩ := hfc
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpvalue⟩ := (M.real_members point).mp (inputReal point (hdomain ▸ hp))
  rw [hpvalue] at h ⊢
  have hpnum : M.mem (M.number (p : ℂ)) (F.domainValue f) := hpvalue ▸ hp
  have both := (functionContinuity_iff_epsilonReal .both f hf p hpnum).mp h
  apply (functionContinuity_iff_epsilonReal side f hf p hpnum).mpr
  intro epsilon hepsilon
  obtain ⟨delta,hdelta,control⟩ := both epsilon hepsilon
  refine ⟨delta,hdelta,?_⟩
  intro input hx hside hnear
  apply control input hx trivial
  change |input-p| < delta
  rwa [continuityDistance_eq_abs side p input hside] at hnear

theorem functionContinuousAtFromSides {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point : M.Value) (hf : RealFunctionValue M f)
    (hp : M.mem point (F.domainValue f))
    (hl : FunctionContinuousAtValue M .left f point)
    (hr : FunctionContinuousAtValue M .right f point) :
    FunctionContinuousAtValue M .both f point := by
  have hfc := hf
  obtain ⟨signature,hfn,inputReal,_⟩ := hfc
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpvalue⟩ := (M.real_members point).mp (inputReal point (hdomain ▸ hp))
  rw [hpvalue] at hl hr ⊢
  have hpnum : M.mem (M.number (p : ℂ)) (F.domainValue f) := hpvalue ▸ hp
  have left := (functionContinuity_iff_epsilonReal .left f hf p hpnum).mp hl
  have right := (functionContinuity_iff_epsilonReal .right f hf p hpnum).mp hr
  apply (functionContinuity_iff_epsilonReal .both f hf p hpnum).mpr
  intro epsilon hepsilon
  obtain ⟨dl,hdl,leftControl⟩ := left epsilon hepsilon
  obtain ⟨dr,hdr,rightControl⟩ := right epsilon hepsilon
  refine ⟨Min.min dl dr,lt_min hdl hdr,?_⟩
  intro input hx _ hnear
  change |input-p| < Min.min dl dr at hnear
  by_cases hside : input ≤ p
  · apply leftControl input hx hside
    rw [continuityDistance_eq_abs .left p input hside]
    exact lt_of_lt_of_le hnear (min_le_left _ _)
  · have hside : p ≤ input := le_of_lt (lt_of_not_ge hside)
    apply rightControl input hx hside
    rw [continuityDistance_eq_abs .right p input hside]
    exact lt_of_lt_of_le hnear (min_le_right _ _)


end Litex

namespace Litex

theorem functionContinuousOfRealUnary {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f) (operation : ℝ → ℝ)
    (hcontinuous : Continuous operation)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue operation x) : FunctionContinuousValue M f := by
  intro point hp
  have hfc := hf
  obtain ⟨signature,hfn,inputReal,_⟩ := hfc
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpoint⟩ := (M.real_members point).mp (inputReal point (hdomain ▸ hp))
  have hpnum : M.mem (M.number (p : ℂ)) (F.domainValue f) := hpoint ▸ hp
  have heq : ∀ x ∈ continuityApproachSet M .both f p,
      observeRealFunction f x = operation x := by
    intro x hx
    have equation := formula (M.number (x : ℂ)) hx.1
    rw [realUnaryValue_number] at equation
    unfold observeRealFunction
    rw [equation,observeRealValue_number]
  rw [hpoint]
  exact (functionContinuity_iff_native .both f hf p hpnum).mpr
    (hcontinuous.continuousAt.continuousWithinAt.congr_of_mem heq ⟨hpnum,trivial⟩)

theorem functionContinuousOfExp {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue Real.exp x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf Real.exp Real.continuous_exp formula

theorem functionContinuousOfSin {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue Real.sin x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf Real.sin Real.continuous_sin formula

theorem functionContinuousOfCos {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue Real.cos x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf Real.cos Real.continuous_cos formula

theorem functionContinuousOfArcsin {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue Real.arcsin x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf Real.arcsin Real.continuous_arcsin formula

theorem functionContinuousOfArccos {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue Real.arccos x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf Real.arccos Real.continuous_arccos formula

theorem functionContinuousOfArctan {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue Real.arctan x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf Real.arctan Real.continuous_arctan formula

theorem functionContinuousOfArccot {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue nativeArccot x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf nativeArccot (continuous_const.sub Real.continuous_arctan) formula

theorem functionContinuousOfSinh {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue Real.sinh x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf Real.sinh Real.continuous_sinh formula

theorem functionContinuousOfCosh {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue Real.cosh x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf Real.cosh Real.continuous_cosh formula

theorem functionContinuousOfTanh {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue Real.tanh x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf Real.tanh (by
    change Continuous (fun x : ℝ => Real.tanh x)
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => ne_of_gt (Real.cosh_pos x))) formula

theorem functionContinuousOfSech {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) →
      F.callValue f x = realUnaryValue nativeSech x) : FunctionContinuousValue M f := by
  exact functionContinuousOfRealUnary f hf nativeSech (continuous_const.div Real.continuous_cosh (fun x => ne_of_gt (Real.cosh_pos x))) formula

end Litex
