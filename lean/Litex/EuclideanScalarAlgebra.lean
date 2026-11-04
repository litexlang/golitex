import Litex.MultivariableContinuity

open Filter
open scoped Topology
namespace Litex
universe u

private def scalarNeighborhood {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point n : M.Value) (allowed : M.Value → Prop) (radius : ℝ) : Set M.Value :=
  {x | M.mem x domain ∧ allowed x ∧
    RealLtValue M (multivariableDistanceValue x point n) (M.number (radius : ℂ))}

private def scalarSourceFilter {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point n : M.Value) (allowed : M.Value → Prop) : Filter M.Value :=
  ⨅ radius : ℝ, ⨅ (_ : 0<radius), Filter.principal (scalarNeighborhood domain point n allowed radius)

private theorem radius_mono {M : Semantics.{u}} {distance : M.Value} {r s : ℝ}
    (h : r≤s) (near : RealLtValue M distance (M.number (r : ℂ))) :
    RealLtValue M distance (M.number (s : ℂ)) := by
  obtain ⟨a,b,ha,hb,hab⟩ := near
  have hb' : b=r := Complex.ofReal_injective (M.number_injective hb).symm
  exact ⟨a,s,ha,rfl,(hb' ▸ hab).trans_le h⟩

private theorem scalarSourceBasis {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point n : M.Value) (allowed : M.Value → Prop) :
    (scalarSourceFilter domain point n allowed).HasBasis (fun radius : ℝ => 0<radius)
      (scalarNeighborhood domain point n allowed) := by
  apply Filter.hasBasis_biInf_principal'
  · intro r hr s hs
    refine ⟨Min.min r s,lt_min hr hs,?_,?_⟩
    · intro x hx
      exact ⟨hx.1,hx.2.1,radius_mono (min_le_left r s) hx.2.2⟩
    · intro x hx
      exact ⟨hx.1,hx.2.1,radius_mono (min_le_right r s) hx.2.2⟩
  · exact ⟨1,zero_lt_one⟩

private def scalarControl {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain f point n value : M.Value) (allowed : M.Value → Prop) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ delta : Obj (M := M) M.Value, In delta RPos ∧
      ∀ x, M.mem x domain → allowed x →
        RealLtValue M (multivariableDistanceValue x point n) (denote delta) →
        RealLtValue M (absValue (M.subValue (F.callValue f x) value)) epsilon

private theorem scalarControl_iff_tendsto {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain f point n value : M.Value) (allowed : M.Value → Prop)
    (hf : ∀ x, M.mem x domain → M.mem (F.callValue f x) (M.standard .real))
    (hv : M.mem value (M.standard .real)) :
    scalarControl domain f point n value allowed ↔
      Tendsto (fun x => observeRealValue (F.callValue f x))
        (scalarSourceFilter domain point n allowed) (𝓝 (observeRealValue value)) := by
  obtain ⟨v,hv⟩ := (M.real_members _).mp hv
  rw [Metric.tendsto_nhds]
  constructor
  · intro control epsilon he
    have hmem : M.mem (M.number (epsilon : ℂ)) (denote (RPos (M := M))) :=
      (positiveReal_members _).mpr ⟨(M.real_members _).mpr ⟨epsilon,rfl⟩,epsilon,rfl,he⟩
    obtain ⟨delta,hd,hcontrol⟩ := control (M.number (epsilon : ℂ)) hmem
    obtain ⟨_,d,hd,hdpos⟩ := (positiveReal_members _).mp hd
    apply (scalarSourceBasis domain point n allowed).eventually_iff.mpr
    refine ⟨d,hdpos,?_⟩
    intro x hx
    have near : RealLtValue M (multivariableDistanceValue x point n) (denote delta) := hd.symm ▸ hx.2.2
    have bound := hcontrol x hx.1 hx.2.1 near
    obtain ⟨a,ha⟩ := (M.real_members _).mp (hf x hx.1)
    rw [ha,hv,scalarError_numbers,realLtValue_numbers] at bound
    simpa only [ha,hv,observeRealValue_number,Real.dist_eq] using bound
  · intro tendsto epsilon he
    obtain ⟨_,e,he,hepos⟩ := (positiveReal_members _).mp he
    obtain ⟨d,hd,hcontrol⟩ := (scalarSourceBasis domain point n allowed).eventually_iff.mp (tendsto e hepos)
    have hdm : M.mem (M.number (d : ℂ)) (M.standard .real) := (M.real_members _).mpr ⟨d,rfl⟩
    let delta := semanticObject (M.number (d : ℂ)) (M.member_isSet hdm)
    refine ⟨delta,?_,?_⟩
    · exact (positiveReal_members _).mpr ⟨hdm,d,rfl,hd⟩
    · intro x hx ha near
      have bound := hcontrol ⟨hx,ha,near⟩
      obtain ⟨a,hvalue⟩ := (M.real_members _).mp (hf x hx)
      rw [hvalue,hv,scalarError_numbers,he,realLtValue_numbers]
      simpa only [hvalue,hv,observeRealValue_number,Real.dist_eq] using bound

private inductive ScalarAlgebraOperation where
  | add | subtract | multiply | divide

private def scalarAlgebraValue {M : Semantics.{u}} (op : ScalarAlgebraOperation)
    (a b : M.Value) : M.Value :=
  match op with
  | .add => M.addValue a b
  | .subtract => M.subValue a b
  | .multiply => M.mulValue a b
  | .divide => M.divValue a b

private noncomputable def scalarAlgebraReal (op : ScalarAlgebraOperation) (a b : ℝ) : ℝ :=
  match op with
  | .add => a+b
  | .subtract => a-b
  | .multiply => a*b
  | .divide => a/b

private theorem scalarAlgebra_numbers {M : Semantics.{u}} (op : ScalarAlgebraOperation)
    (a b : ℝ) (hne : op=.divide → b≠0) :
    scalarAlgebraValue op (M.number (a : ℂ)) (M.number (b : ℂ)) =
      M.number (scalarAlgebraReal op a b : ℂ) := by
  cases op with
  | add => exact (M.add_numbers _ _).trans (congrArg M.number (Complex.ofReal_add _ _).symm)
  | subtract => exact (M.sub_numbers _ _).trans (congrArg M.number (Complex.ofReal_sub _ _).symm)
  | multiply => exact (M.mul_numbers _ _).trans (congrArg M.number (Complex.ofReal_mul _ _).symm)
  | divide => exact (M.div_numbers _ _ (Complex.ofReal_ne_zero.mpr (hne rfl))).trans (congrArg M.number (Complex.ofReal_div _ _).symm)

private theorem observeRealValue_spec {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .real)) : a=M.number (observeRealValue a : ℂ) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp ha
  rw [hr,observeRealValue_number]

private theorem observeRealValue_nonzero {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .real)) (hne : a≠M.number 0) : observeRealValue a≠0 := by
  intro hz
  apply hne
  exact (observeRealValue_spec a ha).trans (by rw [hz,Complex.ofReal_zero])

private theorem observe_scalarAlgebra {M : Semantics.{u}} (op : ScalarAlgebraOperation)
    (a b : M.Value) (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (hne : op=.divide → b≠M.number 0) :
    observeRealValue (scalarAlgebraValue op a b)=scalarAlgebraReal op (observeRealValue a) (observeRealValue b) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp ha
  obtain ⟨s,hs⟩ := (M.real_members _).mp hb
  have hn : op=.divide → s≠0 := by
    intro hop hz
    apply hne hop
    simpa only [hz,Complex.ofReal_zero] using hs
  rw [hr,hs,scalarAlgebra_numbers op r s hn,observeRealValue_number,
    observeRealValue_number,observeRealValue_number]

private theorem scalarControl_binary {M : Semantics.{u}} [F : FunctionSemantics M]
    (op : ScalarAlgebraOperation) (domain f g h point n a b : M.Value) (allowed : M.Value → Prop)
    (hf : ∀ x, M.mem x domain → M.mem (F.callValue f x) (M.standard .real))
    (hg : ∀ x, M.mem x domain → M.mem (F.callValue g x) (M.standard .real))
    (hh : ∀ x, M.mem x domain → M.mem (F.callValue h x) (M.standard .real))
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (hab : M.mem (scalarAlgebraValue op a b) (M.standard .real))
    (formula : ∀ x, M.mem x domain → F.callValue h x=scalarAlgebraValue op (F.callValue f x) (F.callValue g x))
    (hne : op=.divide → b≠M.number 0)
    (first : scalarControl domain f point n a allowed)
    (second : scalarControl domain g point n b allowed) :
    scalarControl domain h point n (scalarAlgebraValue op a b) allowed := by
  have tf := (scalarControl_iff_tendsto domain f point n a allowed hf ha).mp first
  have tg := (scalarControl_iff_tendsto domain g point n b allowed hg hb).mp second
  have hbn : op=.divide → observeRealValue b≠0 := fun hop => observeRealValue_nonzero b hb (hne hop)
  have mapped : Tendsto (fun x => scalarAlgebraReal op (observeRealValue (F.callValue f x)) (observeRealValue (F.callValue g x)))
      (scalarSourceFilter domain point n allowed) (𝓝 (scalarAlgebraReal op (observeRealValue a) (observeRealValue b))) := by
    cases op with
    | add => exact tf.add tg
    | subtract => exact tf.sub tg
    | multiply => exact tf.mul tg
    | divide => exact tf.div tg (hbn rfl)
  have domain_eventually : ∀ᶠ x in scalarSourceFilter domain point n allowed, M.mem x domain :=
    (scalarSourceBasis domain point n allowed).eventually_iff.mpr ⟨1,zero_lt_one,fun _ hx => hx.1⟩
  have nonzero_eventually : ∀ᶠ x in scalarSourceFilter domain point n allowed,
      op=.divide → F.callValue g x≠M.number 0 := by
    by_cases hop : op=.divide
    · have hn := tg.eventually (eventually_ne_nhds (hbn hop))
      filter_upwards [hn] with x hx
      intro _ hz
      apply hx
      rw [hz]
      exact observeRealValue_number 0
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hop h))
  have agrees : (fun x => observeRealValue (F.callValue h x)) =ᶠ[scalarSourceFilter domain point n allowed]
      (fun x => scalarAlgebraReal op (observeRealValue (F.callValue f x)) (observeRealValue (F.callValue g x))) := by
    filter_upwards [domain_eventually,nonzero_eventually] with x hx hne
    rw [formula x hx]
    exact observe_scalarAlgebra op _ _ (hf x hx) (hg x hx) hne
  apply (scalarControl_iff_tendsto domain h point n _ allowed hh hab).mpr
  rw [observe_scalarAlgebra op a b ha hb hne]
  exact mapped.congr' agrees.symm

private theorem continuous_control {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n : M.Value) :
    ScalarMultivariableContinuousAtValue M f point n ↔
      scalarControl (F.domainValue f) f point n (F.callValue f point) (fun _ => True) := by
  constructor
  · intro h epsilon he
    obtain ⟨delta,hd,control⟩ := h epsilon he
    exact ⟨delta,hd,fun x hx _ near => control x hx near⟩
  · intro h epsilon he
    obtain ⟨delta,hd,control⟩ := h epsilon he
    exact ⟨delta,hd,fun x hx near => control x hx True.intro near⟩

private theorem scalarLimitBinary {M : Semantics.{u}} [F : FunctionSemantics M]
    (op : ScalarAlgebraOperation) (f g h point n a b : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hv : M.mem (scalarAlgebraValue op a b) (M.standard .real))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      F.callValue h x=scalarAlgebraValue op (F.callValue f x) (F.callValue g x))
    (hne : op=.divide → b≠M.number 0)
    (first : HasMultivariableScalarLimitValue M f point n a)
    (second : HasMultivariableScalarLimitValue M g point n b) :
    HasMultivariableScalarLimitValue M h point n (scalarAlgebraValue op a b) := by
  obtain ⟨a0,ha,acc,first⟩ := first
  obtain ⟨b0,hb,_,second⟩ := second
  obtain ⟨value,hvalue⟩ := (M.real_members _).mp hv
  refine ⟨value,hvalue,hDf ▸ acc,?_⟩
  exact scalarControl_binary op (F.domainValue h) f g h point n a b
    (fun x => RealLtValue M (M.number 0) (multivariableDistanceValue x point n))
    (fun x hx => multivariableFunctionReturnsReal f n x hf (hDf.symm ▸ hx))
    (fun x hx => multivariableFunctionReturnsReal g n x hg (hDg.symm ▸ hx))
    (fun x hx => multivariableFunctionReturnsReal h n x hh hx)
    ((M.real_members _).mpr ⟨a0,ha⟩) ((M.real_members _).mpr ⟨b0,hb⟩)
    hv formula hne (hDf ▸ first) (hDg ▸ second)

private theorem scalarContinuousBinary {M : Semantics.{u}} [F : FunctionSemantics M]
    (op : ScalarAlgebraOperation) (f g h point n : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hp : M.mem point (F.domainValue h))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      F.callValue h x=scalarAlgebraValue op (F.callValue f x) (F.callValue g x))
    (hne : op=.divide → F.callValue g point≠M.number 0)
    (first : ScalarMultivariableContinuousAtValue M f point n)
    (second : ScalarMultivariableContinuousAtValue M g point n) :
    ScalarMultivariableContinuousAtValue M h point n := by
  have point_value := multivariableFunctionReturnsReal h n point hh hp
  have hvalue : M.mem (scalarAlgebraValue op (F.callValue f point) (F.callValue g point)) (M.standard .real) :=
    formula point hp ▸ point_value
  have first := (continuous_control f point n).mp first
  have second := (continuous_control g point n).mp second
  have combined := scalarControl_binary op (F.domainValue h) f g h point n
    (F.callValue f point) (F.callValue g point) (fun _ => True)
    (fun x hx => multivariableFunctionReturnsReal f n x hf (hDf.symm ▸ hx))
    (fun x hx => multivariableFunctionReturnsReal g n x hg (hDg.symm ▸ hx))
    (fun x hx => multivariableFunctionReturnsReal h n x hh hx)
    (multivariableFunctionReturnsReal f n point hf (hDf.symm ▸ hp))
    (multivariableFunctionReturnsReal g n point hg (hDg.symm ▸ hp))
    hvalue formula hne (hDf ▸ first) (hDg ▸ second)
  apply (continuous_control h point n).mpr
  simpa only [←formula point hp] using combined

/-- Replay the original limit add equation on the exact common domain. -/
theorem scalarMultivariableLimitAdd {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n a b : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hv : M.mem (M.addValue a b) (M.standard .real))
    (formula : ∀ x, M.mem x (F.domainValue h) → F.callValue h x=M.addValue (F.callValue f x) (F.callValue g x))
    (first : HasMultivariableScalarLimitValue M f point n a)
    (second : HasMultivariableScalarLimitValue M g point n b)
    : HasMultivariableScalarLimitValue M h point n (M.addValue a b) :=
  scalarLimitBinary .add f g h point n a b hf hg hh hDf hDg hv formula (by intro impossible; cases impossible) first second

/-- Replay the original limit subtract equation on the exact common domain. -/
theorem scalarMultivariableLimitSubtract {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n a b : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hv : M.mem (M.subValue a b) (M.standard .real))
    (formula : ∀ x, M.mem x (F.domainValue h) → F.callValue h x=M.subValue (F.callValue f x) (F.callValue g x))
    (first : HasMultivariableScalarLimitValue M f point n a)
    (second : HasMultivariableScalarLimitValue M g point n b)
    : HasMultivariableScalarLimitValue M h point n (M.subValue a b) :=
  scalarLimitBinary .subtract f g h point n a b hf hg hh hDf hDg hv formula (by intro impossible; cases impossible) first second

/-- Replay the original limit multiply equation on the exact common domain. -/
theorem scalarMultivariableLimitMultiply {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n a b : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hv : M.mem (M.mulValue a b) (M.standard .real))
    (formula : ∀ x, M.mem x (F.domainValue h) → F.callValue h x=M.mulValue (F.callValue f x) (F.callValue g x))
    (first : HasMultivariableScalarLimitValue M f point n a)
    (second : HasMultivariableScalarLimitValue M g point n b)
    : HasMultivariableScalarLimitValue M h point n (M.mulValue a b) :=
  scalarLimitBinary .multiply f g h point n a b hf hg hh hDf hDg hv formula (by intro impossible; cases impossible) first second

/-- Replay the original limit divide equation on the exact common domain. -/
theorem scalarMultivariableLimitDivide {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n a b : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hv : M.mem (M.divValue a b) (M.standard .real))
    (formula : ∀ x, M.mem x (F.domainValue h) → F.callValue h x=M.divValue (F.callValue f x) (F.callValue g x))
    (first : HasMultivariableScalarLimitValue M f point n a)
    (second : HasMultivariableScalarLimitValue M g point n b)
    (hne : b≠M.number 0)
    : HasMultivariableScalarLimitValue M h point n (M.divValue a b) :=
  scalarLimitBinary .divide f g h point n a b hf hg hh hDf hDg hv formula (fun _ => hne) first second

/-- Replay the original continuous add equation on the exact common domain. -/
theorem scalarMultivariableContinuousAdd {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hp : M.mem point (F.domainValue h))
    (formula : ∀ x, M.mem x (F.domainValue h) → F.callValue h x=M.addValue (F.callValue f x) (F.callValue g x))
    (first : ScalarMultivariableContinuousAtValue M f point n)
    (second : ScalarMultivariableContinuousAtValue M g point n)
    : ScalarMultivariableContinuousAtValue M h point n :=
  scalarContinuousBinary .add f g h point n hf hg hh hDf hDg hp formula (by intro impossible; cases impossible) first second

/-- Replay the original continuous subtract equation on the exact common domain. -/
theorem scalarMultivariableContinuousSubtract {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hp : M.mem point (F.domainValue h))
    (formula : ∀ x, M.mem x (F.domainValue h) → F.callValue h x=M.subValue (F.callValue f x) (F.callValue g x))
    (first : ScalarMultivariableContinuousAtValue M f point n)
    (second : ScalarMultivariableContinuousAtValue M g point n)
    : ScalarMultivariableContinuousAtValue M h point n :=
  scalarContinuousBinary .subtract f g h point n hf hg hh hDf hDg hp formula (by intro impossible; cases impossible) first second

/-- Replay the original continuous multiply equation on the exact common domain. -/
theorem scalarMultivariableContinuousMultiply {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hp : M.mem point (F.domainValue h))
    (formula : ∀ x, M.mem x (F.domainValue h) → F.callValue h x=M.mulValue (F.callValue f x) (F.callValue g x))
    (first : ScalarMultivariableContinuousAtValue M f point n)
    (second : ScalarMultivariableContinuousAtValue M g point n)
    : ScalarMultivariableContinuousAtValue M h point n :=
  scalarContinuousBinary .multiply f g h point n hf hg hh hDf hDg hp formula (by intro impossible; cases impossible) first second

/-- Replay the original continuous divide equation on the exact common domain. -/
theorem scalarMultivariableContinuousDivide {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n : M.Value)
    (hf : RealMultivariableFunctionValue M f n) (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f=F.domainValue h) (hDg : F.domainValue g=F.domainValue h)
    (hp : M.mem point (F.domainValue h))
    (formula : ∀ x, M.mem x (F.domainValue h) → F.callValue h x=M.divValue (F.callValue f x) (F.callValue g x))
    (first : ScalarMultivariableContinuousAtValue M f point n)
    (second : ScalarMultivariableContinuousAtValue M g point n)
    (hne : F.callValue g point≠M.number 0)
    : ScalarMultivariableContinuousAtValue M h point n :=
  scalarContinuousBinary .divide f g h point n hf hg hh hDf hDg hp formula (fun _ => hne) first second

end Litex
