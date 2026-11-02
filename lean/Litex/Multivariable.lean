import Litex.Derivative

universe u v w x r

open Filter
open scoped Topology

namespace Litex

def realVectorSetValue {M : Semantics.{u}} [F : FunctionSemantics M] (dimension : M.Value) : M.Value :=
  F.fnSetValue (F.sepValue (closedRangeValue (M.number 1) dimension) (fun _ => True)) (M.standard .real)

def multivariableDifferenceValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b dimension : M.Value) : M.Value :=
  F.graphValue (F.sepValue (closedRangeValue (M.number 1) dimension) (fun _ => True))
    (M.standard .real) (fun k => M.subValue (F.callValue a k) (F.callValue b k))

noncomputable def multivariableDistanceValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b dimension : M.Value) : M.Value :=
  sqrtValue (M.number (finiteAggregateValue false (closedRangeValue (M.number 1) dimension)
    (fun k => ((‖NativeBridge.complexValue (F.callValue (multivariableDifferenceValue a b dimension) k)‖ ^ 2 : ℝ) : ℂ))))

def RealMultivariableFunctionValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f dimension : M.Value) : Prop :=
  ∃ signature : FunctionSignature M,
    M.mem f (F.fnSetValue signature.domain signature.target) ∧
    (∀ input, M.mem input signature.domain → M.mem input (realVectorSetValue dimension)) ∧
    (∀ output, M.mem output signature.target → M.mem output (M.standard .real))

def MultivariableAccumulationValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (domain point dimension : M.Value) : Prop :=
  ∀ radius, M.mem radius (denote (RPos (M := M))) →
    ∃ input : Obj (M := M) M.Value, M.mem (denote input) domain ∧
      RealLtValue M (M.number 0) (multivariableDistanceValue (denote input) point dimension) ∧
      RealLtValue M (multivariableDistanceValue (denote input) point dimension) radius

def MultivariableScalarEpsilonValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point dimension value : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ delta : Obj (M := M) M.Value, M.mem (denote delta) (denote (RPos (M := M))) ∧
      ∀ input, M.mem input (F.domainValue f) →
        RealLtValue M (M.number 0) (multivariableDistanceValue input point dimension) →
        RealLtValue M (multivariableDistanceValue input point dimension) (denote delta) →
        RealLtValue M (absValue (M.subValue (F.callValue f input) value)) epsilon

def HasMultivariableScalarLimitValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point dimension value : M.Value) : Prop :=
  ∃ r : ℝ, value=M.number (r : ℂ) ∧
    MultivariableAccumulationValue M (F.domainValue f) point dimension ∧
    MultivariableScalarEpsilonValue M f point dimension value

theorem multivariableFunctionReturnsReal {M : Semantics.{u}} [F : FunctionSemantics M]
    (f dimension input : M.Value) (hf : RealMultivariableFunctionValue M f dimension)
    (hi : M.mem input (F.domainValue f)) : M.mem (F.callValue f input) (M.standard .real) := by
  obtain ⟨signature,hfn,_,hout⟩ := hf
  apply hout
  exact F.call_mem _ _ _ _ hfn ((F.domainValue_eq signature.domain_isSet hfn) ▸ hi)

theorem scalarError_numbers {M : Semantics.{u}} (r s : ℝ) :
    absValue (M.subValue (M.number (r : ℂ)) (M.number (s : ℂ)))=M.number ((|r-s| : ℝ) : ℂ) := by
  rw [M.sub_numbers,←Complex.ofReal_sub,absValue_number]

theorem multivariableScalarLimitUnique {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point dimension value other : M.Value) (hf : RealMultivariableFunctionValue M f dimension)
    (h : HasMultivariableScalarLimitValue M f point dimension value)
    (k : HasMultivariableScalarLimitValue M f point dimension other) : value=other := by
  obtain ⟨r,hr,ha,he⟩ := h
  obtain ⟨s,hs,_,hk⟩ := k
  rw [hr] at he
  rw [hs] at hk
  suffices r=s by rw [hr,hs,this]
  by_contra hne
  let epsilon : ℝ := |r-s|/3
  have hepsilon : 0<epsilon := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
  have hepsmem : M.mem (M.number (epsilon : ℂ)) (denote (RPos (M := M))) :=
    (positiveReal_members _).mpr ⟨(M.real_members _).mpr ⟨epsilon,rfl⟩,epsilon,rfl,hepsilon⟩
  obtain ⟨d,hd,hcontrol⟩ := he _ hepsmem
  obtain ⟨e,he,hecontrol⟩ := hk _ hepsmem
  obtain ⟨dr,hdr,hdrpos⟩ := NativeBridge.realWitnessOfPositive d (inRPos_positive d hd)
  obtain ⟨er,her,herpos⟩ := NativeBridge.realWitnessOfPositive e (inRPos_positive e he)
  let radius : ℝ := Min.min dr er
  have hrad : 0<radius := lt_min hdrpos herpos
  have hradmem : M.mem (M.number (radius : ℂ)) (denote (RPos (M := M))) :=
    (positiveReal_members _).mpr ⟨(M.real_members _).mpr ⟨radius,rfl⟩,radius,rfl,hrad⟩
  obtain ⟨input,hinput,hpositive,hclose⟩ := ha _ hradmem
  obtain ⟨distance,bound,hdistance,hbound,hsmall⟩ := hclose
  have hradbound : radius=bound := Complex.ofReal_injective (M.number_injective hbound)
  subst bound
  have hdsmall : distance<dr := lt_of_lt_of_le hsmall (min_le_left dr er)
  have hesmall : distance<er := lt_of_lt_of_le hsmall (min_le_right dr er)
  have withinD : RealLtValue M (multivariableDistanceValue (denote input) point dimension) (denote d) :=
    ⟨distance,dr,hdistance,hdr,hdsmall⟩
  have withinE : RealLtValue M (multivariableDistanceValue (denote input) point dimension) (denote e) :=
    ⟨distance,er,hdistance,her,hesmall⟩
  have hbound := hcontrol _ hinput hpositive withinD
  have hother := hecontrol _ hinput hpositive withinE
  obtain ⟨y,hy⟩ := (M.real_members _).mp (multivariableFunctionReturnsReal f dimension _ hf hinput)
  rw [hy,scalarError_numbers] at hbound hother
  have hfirst := (realLtValue_numbers _ _).mp hbound
  have hsecond := (realLtValue_numbers _ _).mp hother
  have htriangle : |r-s|≤|y-r|+|y-s| := by
    have heq : r-s=-(y-r)+(y-s) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  dsimp [epsilon] at hfirst hsecond
  have hpos : 0 < |r-s| := abs_pos.mpr (sub_ne_zero.mpr hne)
  linarith

theorem multivariableScalarCandidateReal {M : Semantics.{u}} [FunctionSemantics M]
    (f point dimension value : M.Value) (h : HasMultivariableScalarLimitValue M f point dimension value) :
    M.mem value (M.standard .real) := by
  obtain ⟨r,hr,_⟩ := h
  exact (M.real_members _).mpr ⟨r,hr⟩

noncomputable def multivariableScalarLimitValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point dimension : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasMultivariableScalarLimitValue M f point dimension value then
    Classical.choose h else M.number 0

theorem multivariableScalarLimitValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point dimension : M.Value) (h : ∃ value, HasMultivariableScalarLimitValue M f point dimension value) :
    HasMultivariableScalarLimitValue M f point dimension (multivariableScalarLimitValue f point dimension) := by
  classical
  unfold multivariableScalarLimitValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure MultivariableScalarLimitObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  dimension : Obj (M := M) γ

noncomputable instance multivariableScalarLimitRepresentation {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MultivariableScalarLimitObj (M := M) α β γ) where
  wd p := In p.dimension NPos ∧
    RealMultivariableFunctionValue M (denote p.function) (denote p.dimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.dimension)) ∧
    ∃ value : Obj (M := M) M.Value, In value R ∧
      HasMultivariableScalarLimitValue M (denote p.function) (denote p.point) (denote p.dimension) (denote value)
  denote p := multivariableScalarLimitValue (denote p.function) (denote p.point) (denote p.dimension)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2
    exact M.member_isSet (multivariableScalarCandidateReal _ _ _ _
      (multivariableScalarLimitValueSelected _ _ _ ⟨denote value,hc⟩))

noncomputable def multivariableScalarLimit {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (f : Obj (M := M) α) (p : Obj (M := M) β) (n : Obj (M := M) γ)
    (hn : In n NPos) (hf : RealMultivariableFunctionValue M (denote f) (denote n))
    (hp : M.mem (denote p) (realVectorSetValue (denote n)))
    (existsValue : ∃ value : Obj (M := M) M.Value, In value R ∧
      HasMultivariableScalarLimitValue M (denote f) (denote p) (denote n) (denote value)) :
    Obj (M := M) (MultivariableScalarLimitObj (M := M) α β γ) := ⟨⟨f,p,n⟩,hn,hf,hp,existsValue⟩

theorem multivariableScalarExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point dimension value : M.Value) (h : HasMultivariableScalarLimitValue M f point dimension value) :
    ∃ v : Obj (M := M) M.Value, In v R ∧ HasMultivariableScalarLimitValue M f point dimension (denote v) := by
  have hr := multivariableScalarCandidateReal f point dimension value h
  exact ⟨semanticObject value (M.member_isSet hr),hr,h⟩

theorem multivariableScalarLimitInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MultivariableScalarLimitObj (M := M) α β γ)) : In p R := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2
  exact multivariableScalarCandidateReal _ _ _ _ (multivariableScalarLimitValueSelected _ _ _ ⟨denote value,hc⟩)

theorem multivariableScalarLimitEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MultivariableScalarLimitObj (M := M) α β γ))
    (value : M.Value) (h : HasMultivariableScalarLimitValue M (denote p.val.function)
      (denote p.val.point) (denote p.val.dimension) value) : denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2
  exact multivariableScalarLimitUnique _ _ _ _ _ p.wd.2.1
    (multivariableScalarLimitValueSelected _ _ _ ⟨denote v,hc⟩) h

end Litex

namespace Litex

theorem finiteMagnitudeCoordinateBound {M : Semantics.{u}} (A : M.Value) (g : M.Value → ℂ)
    (finiteA : (memberSet A).Finite) (index : M.Value) (hi : M.mem index A) :
    ∃ r : ℝ, 0 ≤ r ∧
      finiteAggregateValue false A (fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ)) = (r : ℂ) ∧
      ‖g index‖ ≤ Real.sqrt r := by
  classical
  let r := ∑ x ∈ finiteA.toFinset, ‖g x‖ ^ 2
  have hr : 0 ≤ r := Finset.sum_nonneg (fun x hx => sq_nonneg (‖g x‖))
  refine ⟨r,hr,?_,?_⟩
  · unfold finiteAggregateValue
    rw [dif_pos finiteA]
    simp only [Bool.false_eq_true,↓reduceIte]
    exact (map_sum Complex.ofRealHom (fun x => ‖g x‖ ^ 2) finiteA.toFinset).symm
  · have hsingle : ‖g index‖ ^ 2 ≤ r :=
      Finset.single_le_sum (fun x hx => sq_nonneg (‖g x‖)) (finiteA.mem_toFinset.mpr hi)
    calc
      ‖g index‖ = Real.sqrt (‖g index‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt hsingle

theorem multivariableDistanceCoordinateBound {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b dimension index : M.Value) (hn : M.mem dimension (M.standard .natural))
    (ha : M.mem a (realVectorSetValue dimension)) (hb : M.mem b (realVectorSetValue dimension))
    (hi : M.mem index (closedRangeValue (M.number 1) dimension)) :
    ∃ r s t : ℝ, F.callValue a index=M.number (r : ℂ) ∧ F.callValue b index=M.number (s : ℂ) ∧
      multivariableDistanceValue a b dimension=M.number (t : ℂ) ∧ |r-s| ≤ t := by
  let length := semanticObject dimension (M.member_isSet hn)
  have finiteIndices : (memberSet (closedRangeValue (M.number 1) dimension)).Finite :=
    matrixIndexFinite length hn
  let D := F.sepValue (closedRangeValue (M.number 1) dimension) (fun _ => True)
  have hindex : M.mem index D := (F.sep_members _ _ _).mpr ⟨hi,True.intro⟩
  have returns : ∀ k, M.mem k D → M.mem
      (M.subValue (F.callValue a k) (F.callValue b k)) (M.standard .real) := by
    intro k hk
    obtain ⟨r,hr⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ ha hk)
    obtain ⟨s,hs⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hb hk)
    rw [hr,hs,M.sub_numbers,←Complex.ofReal_sub]
    exact (M.real_members _).mpr ⟨r-s,rfl⟩
  obtain ⟨r,hr⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ ha hindex)
  obtain ⟨s,hs⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hb hindex)
  let g := fun k => NativeBridge.complexValue (F.callValue (multivariableDifferenceValue a b dimension) k)
  have hgi : g index=((r-s : ℝ) : ℂ) := by
    dsimp only [g,multivariableDifferenceValue]
    rw [F.call_graphValue _ _ _ returns _ hindex,hr,hs,M.sub_numbers,
      NativeBridge.complexValue_number,←Complex.ofReal_sub]
  obtain ⟨sum,hsum,hsumvalue,hbound⟩ := finiteMagnitudeCoordinateBound _ g finiteIndices index hi
  refine ⟨r,s,Real.sqrt sum,hr,hs,?_,?_⟩
  · unfold multivariableDistanceValue
    rw [hsumvalue,sqrtValue_number]
  · simpa only [hgi,Complex.norm_real,Real.norm_eq_abs] using hbound

theorem realVectorValueExt {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b dimension : M.Value) (ha : M.mem a (realVectorSetValue dimension))
    (hb : M.mem b (realVectorSetValue dimension))
    (same : ∀ i, M.mem i (closedRangeValue (M.number 1) dimension) → F.callValue a i=F.callValue b i) : a=b := by
  let D := F.sepValue (closedRangeValue (M.number 1) dimension) (fun _ => True)
  have hfa : IsFunctionGraph F.pairValue D (M.standard .real) a := (F.fnSet_members _ _ _).mp ha
  have hfb : IsFunctionGraph F.pairValue D (M.standard .real) b := (F.fnSet_members _ _ _).mp hb
  apply F.graph_ext D (M.standard .real) a b hfa hfb
  intro i value
  constructor
  · intro hx
    obtain ⟨hi,hy⟩ := FiniteFunction.graph_pair_value hfa hx
    rw [hy,same i ((F.sep_members _ _ _).mp hi).1]
    exact F.call_graph _ _ _ _ hfb hi
  · intro hx
    obtain ⟨hi,hy⟩ := FiniteFunction.graph_pair_value hfb hx
    rw [hy,←same i ((F.sep_members _ _ _).mp hi).1]
    exact F.call_graph _ _ _ _ hfa hi

end Litex

namespace Litex

def VectorMultivariableFunctionValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f n m : M.Value) : Prop :=
  ∃ signature : FunctionSignature M,
    M.mem f (F.fnSetValue signature.domain signature.target) ∧
    (∀ input, M.mem input signature.domain → M.mem input (realVectorSetValue n)) ∧
    (∀ output, M.mem output signature.target → M.mem output (realVectorSetValue m))

def HasMultivariableVectorLimitValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n m value : M.Value) : Prop :=
  M.mem value (realVectorSetValue m) ∧
  MultivariableAccumulationValue M (F.domainValue f) point n ∧
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ delta : Obj (M := M) M.Value, M.mem (denote delta) (denote (RPos (M := M))) ∧
      ∀ input, M.mem input (F.domainValue f) →
        RealLtValue M (M.number 0) (multivariableDistanceValue input point n) →
        RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
        RealLtValue M (multivariableDistanceValue (F.callValue f input) value m) epsilon

theorem multivariableAccumulationCommonPoint {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point n : M.Value) (h : MultivariableAccumulationValue M domain point n)
    (d e : Obj (M := M) M.Value) (hd : In d RPos) (he : In e RPos) :
    ∃ input : Obj (M := M) M.Value, M.mem (denote input) domain ∧
      RealLtValue M (M.number 0) (multivariableDistanceValue (denote input) point n) ∧
      RealLtValue M (multivariableDistanceValue (denote input) point n) (denote d) ∧
      RealLtValue M (multivariableDistanceValue (denote input) point n) (denote e) := by
  obtain ⟨dr,hdr,hdrpos⟩ := NativeBridge.realWitnessOfPositive d (inRPos_positive d hd)
  obtain ⟨er,her,herpos⟩ := NativeBridge.realWitnessOfPositive e (inRPos_positive e he)
  let radius := Min.min dr er
  have hrad : 0<radius := lt_min hdrpos herpos
  have hradmem : M.mem (M.number (radius : ℂ)) (denote (RPos (M := M))) :=
    (positiveReal_members _).mpr ⟨(M.real_members _).mpr ⟨radius,rfl⟩,radius,rfl,hrad⟩
  obtain ⟨input,hi,hpos,hclose⟩ := h _ hradmem
  obtain ⟨distance,bound,hdistance,hbound,hsmall⟩ := hclose
  have heq : radius=bound := Complex.ofReal_injective (M.number_injective hbound)
  subst bound
  exact ⟨input,hi,hpos,⟨distance,dr,hdistance,hdr,lt_of_lt_of_le hsmall (min_le_left dr er)⟩,
    ⟨distance,er,hdistance,her,lt_of_lt_of_le hsmall (min_le_right dr er)⟩⟩

theorem multivariableVectorFunctionReturns {M : Semantics.{u}} [F : FunctionSemantics M]
    (f n m input : M.Value) (hf : VectorMultivariableFunctionValue M f n m)
    (hi : M.mem input (F.domainValue f)) : M.mem (F.callValue f input) (realVectorSetValue m) := by
  obtain ⟨signature,hfn,_,hout⟩ := hf
  exact hout _ (F.call_mem _ _ _ _ hfn ((F.domainValue_eq signature.domain_isSet hfn) ▸ hi))

theorem multivariableVectorLimitUnique {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m value other : M.Value) (hm : M.mem m (M.standard .natural))
    (hf : VectorMultivariableFunctionValue M f n m)
    (h : HasMultivariableVectorLimitValue M f point n m value)
    (k : HasMultivariableVectorLimitValue M f point n m other) : value=other := by
  obtain ⟨hv,ha,he⟩ := h
  obtain ⟨hw,_,hk⟩ := k
  apply realVectorValueExt value other m hv hw
  intro i hi
  have hindex : M.mem i (F.sepValue (closedRangeValue (M.number 1) m) (fun _ => True)) :=
    (F.sep_members _ _ _).mpr ⟨hi,True.intro⟩
  obtain ⟨r,hr⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hv hindex)
  obtain ⟨s,hs⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hw hindex)
  suffices r=s by rw [hr,hs,this]
  by_contra hne
  let epsilon : ℝ := |r-s|/3
  have hepsilon : 0<epsilon := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
  have hepsmem : M.mem (M.number (epsilon : ℂ)) (denote (RPos (M := M))) :=
    (positiveReal_members _).mpr ⟨(M.real_members _).mpr ⟨epsilon,rfl⟩,epsilon,rfl,hepsilon⟩
  obtain ⟨d,hd,hcontrol⟩ := he _ hepsmem
  obtain ⟨e,he,hecontrol⟩ := hk _ hepsmem
  obtain ⟨input,hinput,hpositive,withinD,withinE⟩ :=
    multivariableAccumulationCommonPoint _ _ _ ha d e hd he
  have hbound := hcontrol _ hinput hpositive withinD
  have hother := hecontrol _ hinput hpositive withinE
  have hreturned := multivariableVectorFunctionReturns f n m _ hf hinput
  obtain ⟨y,r',t,hy,hr',ht,hyr⟩ := multivariableDistanceCoordinateBound _ _ m i hm hreturned hv hi
  obtain ⟨z,s',u,hz,hs',hu,hzs⟩ := multivariableDistanceCoordinateBound _ _ m i hm hreturned hw hi
  have hrr : r'=r := Complex.ofReal_injective (M.number_injective (hr'.symm.trans hr))
  have hss : s'=s := Complex.ofReal_injective (M.number_injective (hs'.symm.trans hs))
  have hzy : z=y := Complex.ofReal_injective (M.number_injective (hz.symm.trans hy))
  subst r' s' z
  rw [ht] at hbound
  rw [hu] at hother
  have hfirst := (realLtValue_numbers _ _).mp hbound
  have hsecond := (realLtValue_numbers _ _).mp hother
  have htriangle : |r-s| ≤ |y-r|+|y-s| := by
    have heq : r-s=-(y-r)+(y-s) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  have hpos : 0 < |r-s| := abs_pos.mpr (sub_ne_zero.mpr hne)
  dsimp [epsilon] at hfirst hsecond
  linarith

noncomputable def multivariableVectorLimitValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasMultivariableVectorLimitValue M f point n m value then
    Classical.choose h else M.number 0

theorem multivariableVectorLimitValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m : M.Value) (h : ∃ value, HasMultivariableVectorLimitValue M f point n m value) :
    HasMultivariableVectorLimitValue M f point n m (multivariableVectorLimitValue f point n m) := by
  classical
  unfold multivariableVectorLimitValue
  rw [dif_pos h]
  exact Classical.choose_spec h

universe y
structure MultivariableVectorLimitObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x) (δ : Type y)
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  inputDimension : Obj (M := M) γ
  outputDimension : Obj (M := M) δ

noncomputable instance multivariableVectorLimitRepresentation {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MultivariableVectorLimitObj (M := M) α β γ δ) where
  wd p := In p.inputDimension NPos ∧ In p.outputDimension NPos ∧
    VectorMultivariableFunctionValue M (denote p.function) (denote p.inputDimension) (denote p.outputDimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.inputDimension)) ∧
    ∃ value : Obj (M := M) M.Value, M.mem (denote value) (realVectorSetValue (denote p.outputDimension)) ∧
      HasMultivariableVectorLimitValue M (denote p.function) (denote p.point)
        (denote p.inputDimension) (denote p.outputDimension) (denote value)
  denote p := multivariableVectorLimitValue (denote p.function) (denote p.point)
    (denote p.inputDimension) (denote p.outputDimension)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2.2
    exact M.member_isSet (multivariableVectorLimitValueSelected _ _ _ _ ⟨denote value,hc⟩).1

noncomputable def multivariableVectorLimit {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (f : Obj (M := M) α) (p : Obj (M := M) β) (n : Obj (M := M) γ) (m : Obj (M := M) δ)
    (hn : In n NPos) (hm : In m NPos)
    (hf : VectorMultivariableFunctionValue M (denote f) (denote n) (denote m))
    (hp : M.mem (denote p) (realVectorSetValue (denote n)))
    (existsValue : ∃ value : Obj (M := M) M.Value, M.mem (denote value) (realVectorSetValue (denote m)) ∧
      HasMultivariableVectorLimitValue M (denote f) (denote p) (denote n) (denote m) (denote value)) :
    Obj (M := M) (MultivariableVectorLimitObj (M := M) α β γ δ) := ⟨⟨f,p,n,m⟩,hn,hm,hf,hp,existsValue⟩

theorem multivariableVectorExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m value : M.Value) (h : HasMultivariableVectorLimitValue M f point n m value) :
    ∃ v : Obj (M := M) M.Value, M.mem (denote v) (realVectorSetValue m) ∧
      HasMultivariableVectorLimitValue M f point n m (denote v) :=
  ⟨semanticObject value (M.member_isSet h.1),h.1,h⟩

theorem multivariableVectorLimitInVector {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MultivariableVectorLimitObj (M := M) α β γ δ)) :
    M.mem (denote p) (realVectorSetValue (denote p.val.outputDimension)) := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2.2
  exact (multivariableVectorLimitValueSelected _ _ _ _ ⟨denote value,hc⟩).1

theorem multivariableVectorLimitEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MultivariableVectorLimitObj (M := M) α β γ δ))
    (value : M.Value) (h : HasMultivariableVectorLimitValue M (denote p.val.function)
      (denote p.val.point) (denote p.val.inputDimension) (denote p.val.outputDimension) value) : denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2.2
  exact multivariableVectorLimitUnique _ _ _ _ _ _ (inNPos_natural _ p.wd.2.1) p.wd.2.2.1
    (multivariableVectorLimitValueSelected _ _ _ _ ⟨denote v,hc⟩) h
end Litex

namespace Litex

noncomputable def identityMatrixValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (n : M.Value) : M.Value :=
  F.graphValue (F.sepValue (FiniteFunction.cartValue ![
    closedRangeValue (M.number 1) n,closedRangeValue (M.number 1) n]) (fun _=>True))
    (M.standard .real) matrixIdentityBody

noncomputable def coordinatePathValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (point n coordinate displacement : M.Value) : M.Value :=
  F.graphValue (F.sepValue (closedRangeValue (M.number 1) n) (fun _=>True)) (M.standard .real)
    (fun k=>M.addValue (F.callValue point k) (M.mulValue displacement
      (F.callValue (identityMatrixValue n) (FiniteFunction.pack2 k coordinate))))

def PartialInteriorValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n coordinate : M.Value) : Prop :=
  ∃ radius : Obj (M := M) M.Value, In radius RPos ∧
    ∀ h, M.mem h (M.standard .real) → RealLtValue M (absValue h) (denote radius) →
      M.mem (coordinatePathValue point n coordinate h) (F.domainValue f)

noncomputable def partialQuotientValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n coordinate : M.Value) : M.Value :=
  F.graphValue (F.sepValue (M.standard .real) (fun h=>h≠M.number 0 ∧
    M.mem (coordinatePathValue point n coordinate h) (F.domainValue f))) (M.standard .real)
    (fun h=>M.divValue (M.subValue (F.callValue f (coordinatePathValue point n coordinate h))
      (F.callValue f point)) h)

def HasPartialDerivativeAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n coordinate value : M.Value) : Prop :=
  PartialInteriorValue M f point n coordinate ∧
    HasFiniteFunctionLimitValue M .both (partialQuotientValue f point n coordinate) (M.number 0) value

theorem partialDerivativeCandidateReal {M : Semantics.{u}} [FunctionSemantics M]
    (f point n coordinate value : M.Value) (h : HasPartialDerivativeAtValue M f point n coordinate value) :
    M.mem value (M.standard .real) := by
  obtain ⟨_,_,r,_,hr,_⟩ := h
  exact (M.real_members _).mpr ⟨r,hr⟩

theorem partialDerivativeCandidatesEqual {M : Semantics.{u}} [FunctionSemantics M]
    (f point n coordinate value other : M.Value)
    (h : HasPartialDerivativeAtValue M f point n coordinate value)
    (k : HasPartialDerivativeAtValue M f point n coordinate other) : value=other := by
  obtain ⟨_,p,r,hp,hr,ha,he⟩ := h
  obtain ⟨_,q,s,hq,hs,_,hk⟩ := k
  have hpq : p=q := Complex.ofReal_injective (M.number_injective (hp.symm.trans hq))
  subst q
  have hrs := finiteFunctionLimitUnique .both _ p r s ha he hk
  exact hr.trans ((congrArg (fun z : ℝ=>M.number (z : ℂ)) hrs).trans hs.symm)

noncomputable def partialDerivativeValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point n coordinate : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasPartialDerivativeAtValue M f point n coordinate value then
    Classical.choose h else M.number 0

theorem partialDerivativeValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point n coordinate : M.Value) (h : ∃ value, HasPartialDerivativeAtValue M f point n coordinate value) :
    HasPartialDerivativeAtValue M f point n coordinate (partialDerivativeValue f point n coordinate) := by
  classical
  unfold partialDerivativeValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure PartialDerivativeObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x) (δ : Type y)
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  dimension : Obj (M := M) γ
  coordinate : Obj (M := M) δ

noncomputable instance partialDerivativeRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (PartialDerivativeObj (M := M) α β γ δ) where
  wd p := In p.dimension NPos ∧ RealMultivariableFunctionValue M (denote p.function) (denote p.dimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.dimension)) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    M.mem (denote p.coordinate) (closedRangeValue (M.number 1) (denote p.dimension)) ∧
    ∃ value : Obj (M := M) M.Value, In value R ∧ HasPartialDerivativeAtValue M
      (denote p.function) (denote p.point) (denote p.dimension) (denote p.coordinate) (denote value)
  denote p := partialDerivativeValue (denote p.function) (denote p.point) (denote p.dimension) (denote p.coordinate)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2.2.2
    exact M.member_isSet (partialDerivativeCandidateReal _ _ _ _ _
      (partialDerivativeValueSelected _ _ _ _ ⟨denote value,hc⟩))

theorem partialDerivativeExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n coordinate value : M.Value) (h : HasPartialDerivativeAtValue M f point n coordinate value) :
    ∃ v : Obj (M := M) M.Value, In v R ∧ HasPartialDerivativeAtValue M f point n coordinate (denote v) :=
  ⟨semanticObject value (M.member_isSet (partialDerivativeCandidateReal _ _ _ _ _ h)),
    partialDerivativeCandidateReal _ _ _ _ _ h,h⟩

theorem partialDerivativeInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (PartialDerivativeObj (M := M) α β γ δ)) : In p R := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2.2.2
  exact partialDerivativeCandidateReal _ _ _ _ _ (partialDerivativeValueSelected _ _ _ _ ⟨denote value,hc⟩)

theorem partialDerivativeEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (PartialDerivativeObj (M := M) α β γ δ)) (value : M.Value)
    (h : HasPartialDerivativeAtValue M (denote p.val.function) (denote p.val.point)
      (denote p.val.dimension) (denote p.val.coordinate) value) : denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2.2.2
  exact partialDerivativeCandidatesEqual _ _ _ _ _ _
    (partialDerivativeValueSelected _ _ _ _ ⟨denote v,hc⟩) h
end Litex

namespace Litex

def HasGradientAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n value : M.Value) : Prop :=
  M.mem value (realVectorSetValue n) ∧ ∀ coordinate,
    M.mem coordinate (closedRangeValue (M.number 1) n) →
      HasPartialDerivativeAtValue M f point n coordinate (F.callValue value coordinate)

theorem gradientCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value other : M.Value) (h : HasGradientAtValue M f point n value)
    (k : HasGradientAtValue M f point n other) : value=other := by
  apply realVectorValueExt value other n h.1 k.1
  intro i hi
  exact partialDerivativeCandidatesEqual _ _ _ _ _ _ (h.2 i hi) (k.2 i hi)

noncomputable def gradientValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasGradientAtValue M f point n value then Classical.choose h else M.number 0

theorem gradientValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) (h : ∃ value, HasGradientAtValue M f point n value) :
    HasGradientAtValue M f point n (gradientValue f point n) := by
  classical
  unfold gradientValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure GradientObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  dimension : Obj (M := M) γ

noncomputable instance gradientRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (GradientObj (M := M) α β γ) where
  wd p := In p.dimension NPos ∧ RealMultivariableFunctionValue M (denote p.function) (denote p.dimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.dimension)) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    ∃ value : Obj (M := M) M.Value, M.mem (denote value) (realVectorSetValue (denote p.dimension)) ∧
      HasGradientAtValue M (denote p.function) (denote p.point) (denote p.dimension) (denote value)
  denote p := gradientValue (denote p.function) (denote p.point) (denote p.dimension)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2.2
    exact M.member_isSet (gradientValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem gradientExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n value : M.Value) (h : HasGradientAtValue M f point n value) :
    ∃ v : Obj (M := M) M.Value, M.mem (denote v) (realVectorSetValue n) ∧
      HasGradientAtValue M f point n (denote v) := ⟨semanticObject value (M.member_isSet h.1),h.1,h⟩

theorem gradientInVector {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (GradientObj (M := M) α β γ)) :
    M.mem (denote p) (realVectorSetValue (denote p.val.dimension)) := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2.2
  exact (gradientValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem gradientEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (GradientObj (M := M) α β γ)) (value : M.Value)
    (h : HasGradientAtValue M (denote p.val.function) (denote p.val.point) (denote p.val.dimension) value) :
    denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2.2
  exact gradientCandidatesEqual _ _ _ _ _ (gradientValueSelected _ _ _ ⟨denote v,hc⟩) h
end Litex


-- Trace linearity and cyclicity over the original finite matrix domains.
namespace Litex

theorem finiteSumValueAdd {M : Semantics.{u}} (A : M.Value)
    (f g : M.Value → ℂ) (hA : (memberSet A).Finite) :
    finiteAggregateValue false A (fun k => f k + g k) =
      finiteAggregateValue false A f + finiteAggregateValue false A g := by
  classical
  simp only [finiteAggregateValue, dif_pos hA, Bool.false_eq_true, ↓reduceIte]
  exact Finset.sum_add_distrib

theorem finiteSumValueMulLeft {M : Semantics.{u}} (A : M.Value)
    (z : ℂ) (f : M.Value → ℂ) (hA : (memberSet A).Finite) :
    finiteAggregateValue false A (fun k => z * f k) =
      z * finiteAggregateValue false A f := by
  classical
  simp only [finiteAggregateValue, dif_pos hA, Bool.false_eq_true, ↓reduceIte]
  exact (Finset.mul_sum _ _ _).symm

theorem finiteSumValueComm {M : Semantics.{u}} (A B : M.Value)
    (f : M.Value → M.Value → ℂ)
    (hA : (memberSet A).Finite) (hB : (memberSet B).Finite) :
    finiteAggregateValue false A (fun i => finiteAggregateValue false B (f i)) =
      finiteAggregateValue false B (fun j => finiteAggregateValue false A (fun i => f i j)) := by
  classical
  simp only [finiteAggregateValue, dif_pos hA, dif_pos hB, Bool.false_eq_true, ↓reduceIte]
  exact Finset.sum_comm

theorem matrixTraceAdd {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    M.number (matrixTraceValue (denote (matrixEntrywise .add a b n n hn hn ha hb)) n) =
      M.addValue (M.number (matrixTraceValue (denote a) n))
        (M.number (matrixTraceValue (denote b) n)) := by
  rw [M.add_numbers]
  apply congrArg M.number
  unfold matrixTraceValue
  trans finiteAggregateValue false (matrixIndexValue n)
    (fun k => NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 k k)) +
      NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 k k)))
  · apply finiteAggregateValue_congr
    intro k hk
    rw [matrixEntrywiseCall (matrixEntrywise .add a b n n hn hn ha hb) _
      (matrixDomain_pair n n k k hk hk)]
    simp only [matrixEntrywiseBody, matrixEntrywiseValue, matrixEntrywise, FiniteFunction.unpack_pack2]
    obtain ⟨z, hz⟩ := (M.complex_members _).mp
      (F.call_mem _ _ _ _ ha (matrixDomain_pair n n k k hk hk))
    obtain ⟨y, hy⟩ := (M.complex_members _).mp
      (F.call_mem _ _ _ _ hb (matrixDomain_pair n n k k hk hk))
    rw [hz, hy, M.add_numbers, NativeBridge.complexValue_number,
      NativeBridge.complexValue_number, NativeBridge.complexValue_number]
  · exact finiteSumValueAdd _ _ _ (matrixIndexFinite n hn)

theorem matrixTraceScale {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (z : Obj (M := M) α) (a : Obj (M := M) β) (n : Obj (M := M) γ)
    (hz : In z C) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    M.number (matrixTraceValue (denote (matrixScale z a n n hz hn hn ha)) n) =
      M.mulValue (denote z) (M.number (matrixTraceValue (denote a) n)) := by
  rw [NativeBridge.complexValue_spec (denote z) hz, M.mul_numbers]
  apply congrArg M.number
  unfold matrixTraceValue
  trans finiteAggregateValue false (matrixIndexValue n)
    (fun k => NativeBridge.complexValue (denote z) *
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 k k)))
  · apply finiteAggregateValue_congr
    intro k hk
    rw [matrixScaleCall (matrixScale z a n n hz hn hn ha) _
      (matrixDomain_pair n n k k hk hk)]
    simp only [matrixScaleBody, matrixScale, FiniteFunction.unpack_pack2]
    obtain ⟨c, hc⟩ := (M.complex_members _).mp hz
    obtain ⟨y, hy⟩ := (M.complex_members _).mp
      (F.call_mem _ _ _ _ ha (matrixDomain_pair n n k k hk hk))
    rw [hc, hy, M.mul_numbers, NativeBridge.complexValue_number,
      NativeBridge.complexValue_number, NativeBridge.complexValue_number]
  · exact finiteSumValueMulLeft _ _ _ (matrixIndexFinite n hn)

theorem matrixMultiplyEntryComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε))
    (i j : M.Value)
    (hi : M.mem i (matrixIndexValue p.val.rows))
    (hj : M.mem j (matrixIndexValue p.val.cols)) :
    NativeBridge.complexValue (F.callValue (denote p) (FiniteFunction.pack2 i j)) =
      finiteAggregateValue false (matrixIndexValue p.val.inner)
        (fun k => NativeBridge.complexValue (F.callValue (denote p.val.left) (FiniteFunction.pack2 i k)) *
          NativeBridge.complexValue (F.callValue (denote p.val.right) (FiniteFunction.pack2 k j))) := by
  rw [matrixMultiplyCall p _ (matrixDomain_pair p.val.rows p.val.cols i j hi hj)]
  unfold matrixMultiplyBody matrixMultiplyRawBody
  rw [NativeBridge.complexValue_number]
  apply finiteAggregateValue_congr
  intro k hk
  have ht : ∀ q, M.mem q (finiteSeqDomain p.val.inner) →
      M.mem (matrixMultiplyTerm (denote p.val.left) (denote p.val.right)
        (FiniteFunction.pack2 i j) q) (M.standard .complex) := by
    intro q hq
    have hq' := ((F.sep_members _ _ _).mp hq).1
    simp only [matrixMultiplyTerm, FiniteFunction.unpack_pack2]
    exact Semantics.mul_closed
      (F.call_mem _ _ _ _ p.wd.2.2.2.1 (matrixDomain_pair p.val.rows p.val.inner i q hi hq'))
      (F.call_mem _ _ _ _ p.wd.2.2.2.2 (matrixDomain_pair p.val.inner p.val.cols q j hq' hj))
  change NativeBridge.complexValue (F.callValue
    (F.graphValue (finiteSeqDomain p.val.inner) (M.standard .complex)
      (matrixMultiplyTerm (denote p.val.left) (denote p.val.right) (FiniteFunction.pack2 i j))) k) = _
  rw [F.call_graphValue _ _ _ ht k ((F.sep_members _ _ _).mpr ⟨hk, True.intro⟩)]
  simp only [matrixMultiplyTerm, FiniteFunction.unpack_pack2]
  obtain ⟨a, ha⟩ := (M.complex_members _).mp
    (F.call_mem _ _ _ _ p.wd.2.2.2.1 (matrixDomain_pair p.val.rows p.val.inner i k hi hk))
  obtain ⟨b, hb⟩ := (M.complex_members _).mp
    (F.call_mem _ _ _ _ p.wd.2.2.2.2 (matrixDomain_pair p.val.inner p.val.cols k j hk hj))
  rw [ha, hb, M.mul_numbers, NativeBridge.complexValue_number,
    NativeBridge.complexValue_number, NativeBridge.complexValue_number]

theorem matrixTraceCyclic {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (m : Obj (M := M) γ) (n : Obj (M := M) δ) (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain n m) (M.standard .complex))) :
    M.number (matrixTraceValue (denote (matrixMultiply a b m n m hm hn hm ha hb)) m) =
      M.number (matrixTraceValue (denote (matrixMultiply b a n m n hn hm hn hb ha)) n) := by
  apply congrArg M.number
  unfold matrixTraceValue
  calc
    _ = finiteAggregateValue false (matrixIndexValue m) (fun i =>
        finiteAggregateValue false (matrixIndexValue n) (fun j =>
          NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i j)) *
            NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 j i)))) := by
      apply finiteAggregateValue_congr
      intro i hi
      exact matrixMultiplyEntryComplex _ i i hi hi
    _ = finiteAggregateValue false (matrixIndexValue n) (fun j =>
        finiteAggregateValue false (matrixIndexValue m) (fun i =>
          NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i j)) *
            NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 j i)))) :=
      finiteSumValueComm _ _ _ (matrixIndexFinite m hm) (matrixIndexFinite n hn)
    _ = _ := by
      apply finiteAggregateValue_congr
      intro j hj
      rw [matrixMultiplyEntryComplex _ j j hj hj]
      apply finiteAggregateValue_congr
      intro i _hi
      exact mul_comm _ _

end Litex


-- Multiplication by identity and zero preserves the complete finite domains.
namespace Litex

open scoped Classical

theorem matrixSameOfComplexEntries {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (m : Obj (M := M) γ) (n : Obj (M := M) δ)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (h : ∀ i j, M.mem i (matrixIndexValue m) → M.mem j (matrixIndexValue n) →
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i j)) =
        NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 i j))) : Same a b := by
  apply functionExtOnDomain a b (matrixEntrywiseSignature m n .complex)
    (matrixEntrywiseSignature m n .complex) ha hb rfl
  intro q hq
  obtain ⟨i, hi, j, hj, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp
    ((F.sep_members _ _ _).mp hq).1
  have hd := matrixDomain_pair m n i j hi hj
  exact (NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha hd)).trans
    ((congrArg M.number (h i j hi hj)).trans
      (NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ hb hd)).symm)

theorem finiteSumValueSingle {M : Semantics.{u}} (A : M.Value) (f : M.Value → ℂ)
    (hA : (memberSet A).Finite) (k : M.Value) (hk : M.mem k A) :
    finiteAggregateValue false A (fun x => if x = k then f x else 0) = f k := by
  classical
  simp only [finiteAggregateValue, dif_pos hA, Bool.false_eq_true, ↓reduceIte]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _hb hbk
    simp only [if_neg hbk]
  · intro h
    exact (h (hA.mem_toFinset.mpr hk)).elim

theorem identityMatrixEntryComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N)
    (i j : M.Value) (hi : M.mem i (matrixIndexValue n)) (hj : M.mem j (matrixIndexValue n)) :
    NativeBridge.complexValue (F.callValue (denote (identityMatrix n hn)) (FiniteFunction.pack2 i j)) =
      if i = j then 1 else 0 := by
  classical
  rw [identityMatrixCall (identityMatrix n hn) _ (matrixDomain_pair n n i j hi hj)]
  simp only [matrixIdentityBody, FiniteFunction.unpack_pack2]
  by_cases h : i = j
  · subst j
    rw [matrixIdentityEntrySelf, NativeBridge.complexValue_number, if_pos rfl]
  · rw [matrixIdentityEntryDifferent _ _ h, NativeBridge.complexValue_number, if_neg h]

theorem matrixMultiplyIdentityLeft {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Same (matrixMultiply (identityMatrix m hm) a m m n hm hm hn
      (functionRealToComplex (identityMatrixInFnSet _)) ha) a := by
  classical
  let p := matrixMultiply (identityMatrix m hm) a m m n hm hm hn
    (functionRealToComplex (identityMatrixInFnSet _)) ha
  apply matrixSameOfComplexEntries p a m n (matrixMultiplyInFnSet p) ha
  intro i j hi hj
  rw [matrixMultiplyEntryComplex p i j hi hj]
  trans finiteAggregateValue false (matrixIndexValue m)
    (fun k => if k = i then NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 k j)) else 0)
  · apply finiteAggregateValue_congr
    intro k hk
    change NativeBridge.complexValue (F.callValue (denote (identityMatrix m hm)) (FiniteFunction.pack2 i k)) * _ = _
    rw [identityMatrixEntryComplex m hm i k hi hk]
    by_cases h : k = i
    · subst k
      simp [p, matrixMultiply]
    · simp [h, Ne.symm h]
  · exact finiteSumValueSingle _ _ (matrixIndexFinite m hm) i hi

theorem matrixMultiplyIdentityRight {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Same (matrixMultiply a (identityMatrix n hn) m n n hm hn hn ha
      (functionRealToComplex (identityMatrixInFnSet _))) a := by
  classical
  let p := matrixMultiply a (identityMatrix n hn) m n n hm hn hn ha
    (functionRealToComplex (identityMatrixInFnSet _))
  apply matrixSameOfComplexEntries p a m n (matrixMultiplyInFnSet p) ha
  intro i j hi hj
  rw [matrixMultiplyEntryComplex p i j hi hj]
  trans finiteAggregateValue false (matrixIndexValue n)
    (fun k => if k = j then NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i k)) else 0)
  · apply finiteAggregateValue_congr
    intro k hk
    change _ * NativeBridge.complexValue (F.callValue (denote (identityMatrix n hn)) (FiniteFunction.pack2 k j)) = _
    rw [identityMatrixEntryComplex n hn k j hk hj]
    by_cases h : k = j
    · subst k
      simp [p, matrixMultiply]
    · simp [h]
  · exact finiteSumValueSingle _ _ (matrixIndexFinite n hn) j hj

theorem matrixMultiplyZeroRight {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ) (k : Obj (M := M) δ)
    (hm : In m N) (hn : In n N) (hk : In k N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Same (matrixMultiply a (zeroMatrix n k hn hk) m n k hm hn hk ha
      (functionRealToComplex (zeroMatrixInFnSet _))) (zeroMatrix m k hm hk) := by
  let p := matrixMultiply a (zeroMatrix n k hn hk) m n k hm hn hk ha
    (functionRealToComplex (zeroMatrixInFnSet _))
  let z := zeroMatrix m k hm hk
  apply matrixSameOfComplexEntries p z m k (matrixMultiplyInFnSet p)
    (functionRealToComplex (zeroMatrixInFnSet z))
  intro i j hi hj
  rw [matrixMultiplyEntryComplex p i j hi hj,
    zeroMatrixCall z _ (matrixDomain_pair m k i j hi hj), NativeBridge.complexValue_number]
  trans finiteAggregateValue false (matrixIndexValue n) (fun _ => 0)
  · apply finiteAggregateValue_congr
    intro q hq
    change _ * NativeBridge.complexValue (F.callValue (denote (zeroMatrix n k hn hk)) (FiniteFunction.pack2 q j)) = _
    rw [zeroMatrixCall (zeroMatrix n k hn hk) _ (matrixDomain_pair n k q j hq hj), NativeBridge.complexValue_number, mul_zero]
  · simp only [finiteAggregateValue, dif_pos (matrixIndexFinite n hn), Bool.false_eq_true,
      ↓reduceIte, Finset.sum_const_zero]

theorem matrixMultiplyZeroLeft {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ) (k : Obj (M := M) δ)
    (hm : In m N) (hn : In n N) (hk : In k N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Same (matrixMultiply (zeroMatrix k m hk hm) a k m n hk hm hn
      (functionRealToComplex (zeroMatrixInFnSet _)) ha) (zeroMatrix k n hk hn) := by
  let p := matrixMultiply (zeroMatrix k m hk hm) a k m n hk hm hn
    (functionRealToComplex (zeroMatrixInFnSet _)) ha
  let z := zeroMatrix k n hk hn
  apply matrixSameOfComplexEntries p z k n (matrixMultiplyInFnSet p)
    (functionRealToComplex (zeroMatrixInFnSet z))
  intro i j hi hj
  rw [matrixMultiplyEntryComplex p i j hi hj,
    zeroMatrixCall z _ (matrixDomain_pair k n i j hi hj), NativeBridge.complexValue_number]
  trans finiteAggregateValue false (matrixIndexValue m) (fun _ => 0)
  · apply finiteAggregateValue_congr
    intro q hq
    change NativeBridge.complexValue (F.callValue (denote (zeroMatrix k m hk hm)) (FiniteFunction.pack2 i q)) * _ = _
    rw [zeroMatrixCall (zeroMatrix k m hk hm) _ (matrixDomain_pair k m i q hi hq), NativeBridge.complexValue_number, zero_mul]
  · simp only [finiteAggregateValue, dif_pos (matrixIndexFinite m hm), Bool.false_eq_true,
      ↓reduceIte, Finset.sum_const_zero]

end Litex


namespace Litex

noncomputable def realMatrixSetValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (rows cols : M.Value) : M.Value :=
  F.fnSetValue (realMatrixDomainValue rows cols) (M.standard .real)

theorem realMatrixValueExt {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b rows cols : M.Value) (ha : M.mem a (realMatrixSetValue rows cols))
    (hb : M.mem b (realMatrixSetValue rows cols))
    (same : ∀ i j, M.mem i (closedRangeValue (M.number 1) rows) →
      M.mem j (closedRangeValue (M.number 1) cols) →
      F.callValue a (FiniteFunction.pack2 i j) = F.callValue b (FiniteFunction.pack2 i j)) : a=b := by
  have hfa := (F.fnSet_members _ _ _).mp ha
  have hfb := (F.fnSet_members _ _ _).mp hb
  have eqCall : ∀ q, M.mem q (realMatrixDomainValue rows cols) → F.callValue a q=F.callValue b q := by
    intro q hq
    obtain ⟨i,hi,j,hj,rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp
      ((F.sep_members _ _ _).mp hq).1
    exact same i j hi hj
  apply F.graph_ext _ _ a b hfa hfb
  intro q value
  constructor
  · intro h
    obtain ⟨hq,hv⟩ := FiniteFunction.graph_pair_value hfa h
    rw [hv,eqCall q hq]
    exact F.call_graph _ _ _ _ hfb hq
  · intro h
    obtain ⟨hq,hv⟩ := FiniteFunction.graph_pair_value hfb h
    rw [hv,←eqCall q hq]
    exact F.call_graph _ _ _ _ hfa hq

noncomputable def componentFunctionValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (f domain row : M.Value) : M.Value :=
  F.graphValue (F.sepValue domain (fun _ => True)) (M.standard .real)
    (fun input => F.callValue (F.callValue f input) row)

def HasJacobianAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n m value : M.Value) : Prop :=
  M.mem value (realMatrixSetValue m n) ∧
    ∀ row, M.mem row (closedRangeValue (M.number 1) m) →
    ∀ col, M.mem col (closedRangeValue (M.number 1) n) →
      HasPartialDerivativeAtValue M (componentFunctionValue f (F.domainValue f) row)
        point n col (F.callValue value (FiniteFunction.pack2 row col))

theorem jacobianCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m value other : M.Value) (h : HasJacobianAtValue M f point n m value)
    (k : HasJacobianAtValue M f point n m other) : value=other := by
  apply realMatrixValueExt value other m n h.1 k.1
  intro i j hi hj
  exact partialDerivativeCandidatesEqual _ _ _ _ _ _ (h.2 i hi j hj) (k.2 i hi j hj)

noncomputable def jacobianValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasJacobianAtValue M f point n m value then Classical.choose h else M.number 0

theorem jacobianValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m : M.Value) (h : ∃ value, HasJacobianAtValue M f point n m value) :
    HasJacobianAtValue M f point n m (jacobianValue f point n m) := by
  classical
  unfold jacobianValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure JacobianObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x) (δ : Type y)
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  inputDimension : Obj (M := M) γ
  outputDimension : Obj (M := M) δ

noncomputable instance jacobianRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (JacobianObj (M := M) α β γ δ) where
  wd p := In p.inputDimension NPos ∧ In p.outputDimension NPos ∧
    VectorMultivariableFunctionValue M (denote p.function) (denote p.inputDimension) (denote p.outputDimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.inputDimension)) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    ∃ value : Obj (M := M) M.Value,
      M.mem (denote value) (realMatrixSetValue (denote p.outputDimension) (denote p.inputDimension)) ∧
      HasJacobianAtValue M (denote p.function) (denote p.point)
        (denote p.inputDimension) (denote p.outputDimension) (denote value)
  denote p := jacobianValue (denote p.function) (denote p.point)
    (denote p.inputDimension) (denote p.outputDimension)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2.2.2
    exact M.member_isSet (jacobianValueSelected _ _ _ _ ⟨denote value,hc⟩).1

theorem jacobianExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m value : M.Value) (h : HasJacobianAtValue M f point n m value) :
    ∃ v : Obj (M := M) M.Value, M.mem (denote v) (realMatrixSetValue m n) ∧
      HasJacobianAtValue M f point n m (denote v) := ⟨semanticObject value (M.member_isSet h.1),h.1,h⟩

theorem jacobianInMatrix {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (JacobianObj (M := M) α β γ δ)) :
    M.mem (denote p) (realMatrixSetValue (denote p.val.outputDimension) (denote p.val.inputDimension)) := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2.2.2
  exact (jacobianValueSelected _ _ _ _ ⟨denote value,hc⟩).1

theorem jacobianEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (JacobianObj (M := M) α β γ δ)) (value : M.Value)
    (h : HasJacobianAtValue M (denote p.val.function) (denote p.val.point)
      (denote p.val.inputDimension) (denote p.val.outputDimension) value) : denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2.2.2
  exact jacobianCandidatesEqual _ _ _ _ _ _ (jacobianValueSelected _ _ _ _ ⟨denote v,hc⟩) h

end Litex

namespace Litex

theorem finiteSumValueMulRight {M : Semantics.{u}} (A : M.Value)
    (f : M.Value → ℂ) (z : ℂ) (hA : (memberSet A).Finite) :
    finiteAggregateValue false A (fun k => f k * z) =
      finiteAggregateValue false A f * z := by
  classical
  simp only [finiteAggregateValue, dif_pos hA, Bool.false_eq_true, ↓reduceIte]
  exact (Finset.sum_mul _ _ _).symm

theorem finiteSumValueMulAssoc {M : Semantics.{u}} (A B : M.Value)
    (f : M.Value → ℂ) (g : M.Value → M.Value → ℂ) (h : M.Value → ℂ)
    (hA : (memberSet A).Finite) (hB : (memberSet B).Finite) :
    finiteAggregateValue false B (fun j => finiteAggregateValue false A (fun i => f i * g i j) * h j) =
      finiteAggregateValue false A (fun i => f i * finiteAggregateValue false B (fun j => g i j * h j)) := by
  calc
    _ = finiteAggregateValue false B (fun j =>
        finiteAggregateValue false A (fun i => (f i * g i j) * h j)) := by
      apply finiteAggregateValue_congr
      intro j _hj
      exact (finiteSumValueMulRight A _ (h j) hA).symm
    _ = finiteAggregateValue false A (fun i =>
        finiteAggregateValue false B (fun j => (f i * g i j) * h j)) :=
      finiteSumValueComm B A _ hB hA
    _ = _ := by
      apply finiteAggregateValue_congr
      intro i _hi
      rw [← finiteSumValueMulLeft B (f i) _ hB]
      apply finiteAggregateValue_congr
      intro j _hj
      exact mul_assoc _ _ _

theorem matrixAddEntryComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ))
    (hop : p.val.operation = .add) (i j : M.Value)
    (hi : M.mem i (matrixIndexValue p.val.rows)) (hj : M.mem j (matrixIndexValue p.val.cols)) :
    NativeBridge.complexValue (F.callValue (denote p) (FiniteFunction.pack2 i j)) =
      NativeBridge.complexValue (F.callValue (denote p.val.left) (FiniteFunction.pack2 i j)) +
        NativeBridge.complexValue (F.callValue (denote p.val.right) (FiniteFunction.pack2 i j)) := by
  rw [matrixEntrywiseCall p _ (matrixDomain_pair p.val.rows p.val.cols i j hi hj)]
  simp only [matrixEntrywiseBody, hop, matrixEntrywiseValue, FiniteFunction.unpack_pack2]
  obtain ⟨a, ha⟩ := (M.complex_members _).mp
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_pair p.val.rows p.val.cols i j hi hj))
  obtain ⟨b, hb⟩ := (M.complex_members _).mp
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_pair p.val.rows p.val.cols i j hi hj))
  rw [ha, hb, M.add_numbers, NativeBridge.complexValue_number,
    NativeBridge.complexValue_number, NativeBridge.complexValue_number]

theorem matrixMultiplyAssociative {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r} {ζ : Type y} {η : Type*}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε] [Representation M ζ] [Representation M η]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (m : Obj (M := M) δ) (k : Obj (M := M) ε) (p : Obj (M := M) ζ) (n : Obj (M := M) η)
    (hm : In m N) (hk : In k N) (hp : In p N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain k p) (M.standard .complex)))
    (hc : M.mem (denote c) (F.fnSetValue (matrixDomain p n) (M.standard .complex))) :
    Same (matrixMultiply (matrixMultiply a b m k p hm hk hp ha hb) c m p n hm hp hn
      (matrixMultiplyInFnSet _) hc)
      (matrixMultiply a (matrixMultiply b c k p n hk hp hn hb hc) m k n hm hk hn ha
        (matrixMultiplyInFnSet _)) := by
  let ab := matrixMultiply a b m k p hm hk hp ha hb
  let bc := matrixMultiply b c k p n hk hp hn hb hc
  let left := matrixMultiply ab c m p n hm hp hn (matrixMultiplyInFnSet ab) hc
  let right := matrixMultiply a bc m k n hm hk hn ha (matrixMultiplyInFnSet bc)
  apply matrixSameOfComplexEntries left right m n (matrixMultiplyInFnSet left) (matrixMultiplyInFnSet right)
  intro i j hi hj
  rw [matrixMultiplyEntryComplex left i j hi hj, matrixMultiplyEntryComplex right i j hi hj]
  change finiteAggregateValue false (matrixIndexValue p) (fun q =>
      NativeBridge.complexValue (F.callValue (denote ab) (FiniteFunction.pack2 i q)) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 q j))) =
    finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote bc) (FiniteFunction.pack2 s j)))
  calc
    _ = finiteAggregateValue false (matrixIndexValue p) (fun q =>
        finiteAggregateValue false (matrixIndexValue k) (fun s =>
          NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
            NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 s q))) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 q j))) := by
      apply finiteAggregateValue_congr
      intro q hq
      exact congrArg (fun z : ℂ => z * NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 q j)))
        (matrixMultiplyEntryComplex ab i q hi hq)
    _ = finiteAggregateValue false (matrixIndexValue k) (fun s =>
        NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
          finiteAggregateValue false (matrixIndexValue p) (fun q =>
            NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 s q)) *
              NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 q j)))) :=
      finiteSumValueMulAssoc _ _ _ _ _ (matrixIndexFinite k hk) (matrixIndexFinite p hp)
    _ = _ := by
      apply finiteAggregateValue_congr
      intro s hs
      exact congrArg (fun z : ℂ => NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) * z)
        (matrixMultiplyEntryComplex bc s j hs hj).symm

theorem matrixMultiplyDistributiveLeft {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r} {ζ : Type y}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε] [Representation M ζ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (m : Obj (M := M) δ) (k : Obj (M := M) ε) (n : Obj (M := M) ζ)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain k n) (M.standard .complex)))
    (hc : M.mem (denote c) (F.fnSetValue (matrixDomain k n) (M.standard .complex))) :
    Same (matrixMultiply a (matrixEntrywise .add b c k n hk hn hb hc) m k n hm hk hn ha
      (matrixEntrywiseInFnSet _))
      (matrixEntrywise .add (matrixMultiply a b m k n hm hk hn ha hb)
        (matrixMultiply a c m k n hm hk hn ha hc) m n hm hn
        (matrixMultiplyInFnSet _) (matrixMultiplyInFnSet _)) := by
  let bc := matrixEntrywise .add b c k n hk hn hb hc
  let ab := matrixMultiply a b m k n hm hk hn ha hb
  let ac := matrixMultiply a c m k n hm hk hn ha hc
  let left := matrixMultiply a bc m k n hm hk hn ha (matrixEntrywiseInFnSet bc)
  let right := matrixEntrywise .add ab ac m n hm hn (matrixMultiplyInFnSet ab) (matrixMultiplyInFnSet ac)
  apply matrixSameOfComplexEntries left right m n (matrixMultiplyInFnSet left) (matrixEntrywiseInFnSet right)
  intro i j hi hj
  rw [matrixMultiplyEntryComplex left i j hi hj, matrixAddEntryComplex right rfl i j hi hj]
  change finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote bc) (FiniteFunction.pack2 s j))) =
    NativeBridge.complexValue (F.callValue (denote ab) (FiniteFunction.pack2 i j)) +
      NativeBridge.complexValue (F.callValue (denote ac) (FiniteFunction.pack2 i j))
  rw [matrixMultiplyEntryComplex ab i j hi hj, matrixMultiplyEntryComplex ac i j hi hj]
  change finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote bc) (FiniteFunction.pack2 s j))) =
    finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 s j))) +
    finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 s j)))
  trans finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 s j)) +
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 s j)))
  · apply finiteAggregateValue_congr
    intro s hs
    rw [matrixAddEntryComplex bc rfl s j hs hj]
    exact mul_add _ _ _
  · exact finiteSumValueAdd _ _ _ (matrixIndexFinite k hk)

theorem matrixMultiplyDistributiveRight {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r} {ζ : Type y}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε] [Representation M ζ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (m : Obj (M := M) δ) (k : Obj (M := M) ε) (n : Obj (M := M) ζ)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hc : M.mem (denote c) (F.fnSetValue (matrixDomain k n) (M.standard .complex))) :
    Same (matrixMultiply (matrixEntrywise .add a b m k hm hk ha hb) c m k n hm hk hn
      (matrixEntrywiseInFnSet _) hc)
      (matrixEntrywise .add (matrixMultiply a c m k n hm hk hn ha hc)
        (matrixMultiply b c m k n hm hk hn hb hc) m n hm hn
        (matrixMultiplyInFnSet _) (matrixMultiplyInFnSet _)) := by
  let ab := matrixEntrywise .add a b m k hm hk ha hb
  let ac := matrixMultiply a c m k n hm hk hn ha hc
  let bc := matrixMultiply b c m k n hm hk hn hb hc
  let left := matrixMultiply ab c m k n hm hk hn (matrixEntrywiseInFnSet ab) hc
  let right := matrixEntrywise .add ac bc m n hm hn (matrixMultiplyInFnSet ac) (matrixMultiplyInFnSet bc)
  apply matrixSameOfComplexEntries left right m n (matrixMultiplyInFnSet left) (matrixEntrywiseInFnSet right)
  intro i j hi hj
  rw [matrixMultiplyEntryComplex left i j hi hj, matrixAddEntryComplex right rfl i j hi hj]
  change finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote ab) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 s j))) =
    NativeBridge.complexValue (F.callValue (denote ac) (FiniteFunction.pack2 i j)) +
      NativeBridge.complexValue (F.callValue (denote bc) (FiniteFunction.pack2 i j))
  rw [matrixMultiplyEntryComplex ac i j hi hj, matrixMultiplyEntryComplex bc i j hi hj]
  change finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote ab) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 s j))) =
    finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 s j))) +
    finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 s j)))
  trans finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 s j)) +
      NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 s j)))
  · apply finiteAggregateValue_congr
    intro s hs
    rw [matrixAddEntryComplex ab rfl i s hi hs]
    exact add_mul _ _ _
  · exact finiteSumValueAdd _ _ _ (matrixIndexFinite k hk)

end Litex


namespace Litex

noncomputable def vectorSumValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (value dimension : M.Value) : M.Value :=
  M.number (finiteAggregateValue false (closedRangeValue (M.number 1) dimension)
    (fun k => NativeBridge.complexValue (F.callValue value k)))

def HasDivergenceAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n value : M.Value) : Prop :=
  M.mem value (M.standard .real) ∧ ∃ diagonal : Obj (M := M) M.Value,
    M.mem (denote diagonal) (realVectorSetValue n) ∧
    (∀ k, M.mem k (closedRangeValue (M.number 1) n) →
      HasPartialDerivativeAtValue M (componentFunctionValue f (F.domainValue f) k)
        point n k (F.callValue (denote diagonal) k)) ∧
    vectorSumValue (denote diagonal) n = value

theorem divergenceCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value other : M.Value) (h : HasDivergenceAtValue M f point n value)
    (k : HasDivergenceAtValue M f point n other) : value=other := by
  obtain ⟨_,a,ha,hparts,hsum⟩ := h
  obtain ⟨_,b,hb,kparts,ksum⟩ := k
  have hab : denote a=denote b := realVectorValueExt _ _ n ha hb (by
    intro i hi
    exact partialDerivativeCandidatesEqual _ _ _ _ _ _ (hparts i hi) (kparts i hi))
  exact hsum.symm.trans ((congrArg (fun v => vectorSumValue v n) hab).trans ksum)

noncomputable def divergenceValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasDivergenceAtValue M f point n value then Classical.choose h else M.number 0

theorem divergenceValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) (h : ∃ value, HasDivergenceAtValue M f point n value) :
    HasDivergenceAtValue M f point n (divergenceValue f point n) := by
  classical
  unfold divergenceValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure DivergenceObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  dimension : Obj (M := M) γ

noncomputable instance divergenceRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (DivergenceObj (M := M) α β γ) where
  wd p := In p.dimension NPos ∧
    VectorMultivariableFunctionValue M (denote p.function) (denote p.dimension) (denote p.dimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.dimension)) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    ∃ value : Obj (M := M) M.Value, In value R ∧
      HasDivergenceAtValue M (denote p.function) (denote p.point) (denote p.dimension) (denote value)
  denote p := divergenceValue (denote p.function) (denote p.point) (denote p.dimension)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2.2
    exact M.member_isSet (divergenceValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem divergenceExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n value : M.Value) (h : HasDivergenceAtValue M f point n value) :
    ∃ v : Obj (M := M) M.Value, In v R ∧ HasDivergenceAtValue M f point n (denote v) :=
  ⟨semanticObject value (M.member_isSet h.1),h.1,h⟩

theorem divergenceInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (DivergenceObj (M := M) α β γ)) : In p R := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2.2
  exact (divergenceValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem divergenceEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (DivergenceObj (M := M) α β γ)) (value : M.Value)
    (h : HasDivergenceAtValue M (denote p.val.function) (denote p.val.point) (denote p.val.dimension) value) :
    denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2.2
  exact divergenceCandidatesEqual _ _ _ _ _ (divergenceValueSelected _ _ _ ⟨denote v,hc⟩) h

end Litex


namespace Litex

def CurlDefinitionValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f domain point value : M.Value) : Prop :=
  ∃ partials : Obj (M := M) M.Value,
    ∃ (_ : M.mem (denote partials) (realVectorSetValue (M.number 6))),
    ∃ (_ : HasPartialDerivativeAtValue M (componentFunctionValue f domain (M.number 3)) point (M.number 3) (M.number 2) (F.callValue (denote partials) (M.number 1))),
    ∃ (_ : HasPartialDerivativeAtValue M (componentFunctionValue f domain (M.number 2)) point (M.number 3) (M.number 3) (F.callValue (denote partials) (M.number 2))),
    ∃ (_ : HasPartialDerivativeAtValue M (componentFunctionValue f domain (M.number 1)) point (M.number 3) (M.number 3) (F.callValue (denote partials) (M.number 3))),
    ∃ (_ : HasPartialDerivativeAtValue M (componentFunctionValue f domain (M.number 3)) point (M.number 3) (M.number 1) (F.callValue (denote partials) (M.number 4))),
    ∃ (_ : HasPartialDerivativeAtValue M (componentFunctionValue f domain (M.number 2)) point (M.number 3) (M.number 1) (F.callValue (denote partials) (M.number 5))),
    ∃ (_ : HasPartialDerivativeAtValue M (componentFunctionValue f domain (M.number 1)) point (M.number 3) (M.number 2) (F.callValue (denote partials) (M.number 6))),
    ∃ (_ : F.callValue value (M.number 1) = M.subValue (F.callValue (denote partials) (M.number 1)) (F.callValue (denote partials) (M.number 2))),
    ∃ (_ : F.callValue value (M.number 2) = M.subValue (F.callValue (denote partials) (M.number 3)) (F.callValue (denote partials) (M.number 4))),
    F.callValue value (M.number 3) = M.subValue (F.callValue (denote partials) (M.number 5)) (F.callValue (denote partials) (M.number 6))

def HasCurlAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point value : M.Value) : Prop :=
  M.mem value (realVectorSetValue (M.number 3)) ∧
    CurlDefinitionValue M f (F.domainValue f) point value

theorem curlCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point value other : M.Value) (h : HasCurlAtValue M f point value)
    (k : HasCurlAtValue M f point other) : value=other := by
  obtain ⟨hv,a,_,a1,a2,a3,a4,a5,a6,e1,e2,e3⟩ := h
  obtain ⟨ho,b,_,b1,b2,b3,b4,b5,b6,k1,k2,k3⟩ := k
  have d1 := partialDerivativeCandidatesEqual _ _ _ _ _ _ a1 b1
  have d2 := partialDerivativeCandidatesEqual _ _ _ _ _ _ a2 b2
  have d3 := partialDerivativeCandidatesEqual _ _ _ _ _ _ a3 b3
  have d4 := partialDerivativeCandidatesEqual _ _ _ _ _ _ a4 b4
  have d5 := partialDerivativeCandidatesEqual _ _ _ _ _ _ a5 b5
  have d6 := partialDerivativeCandidatesEqual _ _ _ _ _ _ a6 b6
  apply realVectorValueExt value other (M.number 3) hv ho
  intro i hi
  obtain ⟨j,rfl,hlo,hhi⟩ := (closedRangeValue_members 1 3 i).mp (by simpa using hi)
  have cases : j=1 ∨ j=2 ∨ j=3 := by omega
  rcases cases with rfl | rfl | rfl
  · simpa using e1.trans ((congrArg₂ M.subValue d1 d2).trans k1.symm)
  · simpa using e2.trans ((congrArg₂ M.subValue d3 d4).trans k2.symm)
  · simpa using e3.trans ((congrArg₂ M.subValue d5 d6).trans k3.symm)

noncomputable def curlValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasCurlAtValue M f point value then Classical.choose h else M.number 0

theorem curlValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point : M.Value) (h : ∃ value, HasCurlAtValue M f point value) :
    HasCurlAtValue M f point (curlValue f point) := by
  classical
  unfold curlValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure CurlObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  function : Obj (M := M) α
  point : Obj (M := M) β

noncomputable instance curlRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (CurlObj (M := M) α β) where
  wd p := VectorMultivariableFunctionValue M (denote p.function) (M.number 3) (M.number 3) ∧
    M.mem (denote p.point) (realVectorSetValue (M.number 3)) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    ∃ value : Obj (M := M) M.Value, M.mem (denote value) (realVectorSetValue (M.number 3)) ∧
      HasCurlAtValue M (denote p.function) (denote p.point) (denote value)
  denote p := curlValue (denote p.function) (denote p.point)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2
    exact M.member_isSet (curlValueSelected _ _ ⟨denote value,hc⟩).1

theorem curlExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point value : M.Value) (h : HasCurlAtValue M f point value) :
    ∃ v : Obj (M := M) M.Value, M.mem (denote v) (realVectorSetValue (M.number 3)) ∧
      HasCurlAtValue M f point (denote v) := ⟨semanticObject value (M.member_isSet h.1),h.1,h⟩

theorem curlInVector {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (CurlObj (M := M) α β)) :
    M.mem (denote p) (realVectorSetValue (M.number 3)) := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2
  exact (curlValueSelected _ _ ⟨denote value,hc⟩).1

theorem curlEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (CurlObj (M := M) α β)) (value : M.Value)
    (h : HasCurlAtValue M (denote p.val.function) (denote p.val.point) value) : denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2
  exact curlCandidatesEqual _ _ _ _ (curlValueSelected _ _ ⟨denote v,hc⟩) h

end Litex

namespace Litex

theorem vectorSameOfComplexEntries {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (h : ∀ i, M.mem i (finiteSeqDomain n) →
      NativeBridge.complexValue (F.callValue (denote a) i) =
        NativeBridge.complexValue (F.callValue (denote b) i)) : Same a b := by
  apply functionExtOnDomain a b (matrixApplySignature n .complex)
    (matrixApplySignature n .complex) ha hb rfl
  intro q hq
  exact (NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha hq)).trans
    ((congrArg M.number (h q hq)).trans
      (NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ hb hq)).symm)

theorem matrixApplyEntryComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ)) (i : M.Value)
    (hi : M.mem i (matrixIndexValue p.val.rows)) :
    NativeBridge.complexValue (F.callValue (denote p) i) =
      finiteAggregateValue false (matrixIndexValue p.val.cols)
        (fun k => NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 i k)) *
          NativeBridge.complexValue (F.callValue (denote p.val.vector) k)) := by
  rw [matrixApplyCall p i ((F.sep_members _ _ _).mpr ⟨hi, True.intro⟩)]
  unfold matrixApplyBody
  rw [NativeBridge.complexValue_number]
  apply finiteAggregateValue_congr
  intro k hk
  have ht : ∀ q, M.mem q (finiteSeqDomain p.val.cols) →
      M.mem (matrixApplyTerm (denote p.val.matrix) (denote p.val.vector) i q)
        (M.standard .complex) := by
    intro q hq
    have hq' := ((F.sep_members _ _ _).mp hq).1
    exact Semantics.mul_closed
      (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_pair p.val.rows p.val.cols i q hi hq'))
      (F.call_mem _ _ _ _ p.wd.2.2.2 hq)
  have hk' : M.mem k (finiteSeqDomain p.val.cols) := (F.sep_members _ _ _).mpr ⟨hk, True.intro⟩
  rw [F.call_graphValue _ _ _ ht k hk']
  unfold matrixApplyTerm
  obtain ⟨a, ha⟩ := (M.complex_members _).mp
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_pair p.val.rows p.val.cols i k hi hk))
  obtain ⟨b, hb⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ p.wd.2.2.2 hk')
  rw [ha, hb, M.mul_numbers, NativeBridge.complexValue_number,
    NativeBridge.complexValue_number, NativeBridge.complexValue_number]

theorem matrixApplyIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (v : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (hv : M.mem (denote v) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Same (matrixApply (identityMatrix n hn) v n n hn hn
      (functionRealToComplex (identityMatrixInFnSet _)) hv) v := by
  classical
  let p := matrixApply (identityMatrix n hn) v n n hn hn
    (functionRealToComplex (identityMatrixInFnSet _)) hv
  apply vectorSameOfComplexEntries p v n (matrixApplyInFnSet p) hv
  intro i hi
  have hi' := ((F.sep_members _ _ _).mp hi).1
  rw [matrixApplyEntryComplex p i hi']
  trans finiteAggregateValue false (matrixIndexValue n)
    (fun k => if k = i then NativeBridge.complexValue (F.callValue (denote v) k) else 0)
  · apply finiteAggregateValue_congr
    intro k hk
    change NativeBridge.complexValue (F.callValue (denote (identityMatrix n hn)) (FiniteFunction.pack2 i k)) * _ = _
    rw [identityMatrixEntryComplex n hn i k hi' hk]
    by_cases h : k = i
    · subst k
      simp [p, matrixApply]
    · simp [h, Ne.symm h]
  · exact finiteSumValueSingle _ _ (matrixIndexFinite n hn) i hi'

theorem matrixApplyCompose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r} {ζ : Type y}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε] [Representation M ζ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (v : Obj (M := M) γ)
    (m : Obj (M := M) δ) (k : Obj (M := M) ε) (n : Obj (M := M) ζ)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain k n) (M.standard .complex)))
    (hv : M.mem (denote v) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Same (matrixApply (matrixMultiply a b m k n hm hk hn ha hb) v m n hm hn
      (matrixMultiplyInFnSet _) hv)
      (matrixApply a (matrixApply b v k n hk hn hb hv) m k hm hk ha (matrixApplyInFnSet _)) := by
  let ab := matrixMultiply a b m k n hm hk hn ha hb
  let bv := matrixApply b v k n hk hn hb hv
  let left := matrixApply ab v m n hm hn (matrixMultiplyInFnSet ab) hv
  let right := matrixApply a bv m k hm hk ha (matrixApplyInFnSet bv)
  apply vectorSameOfComplexEntries left right m (matrixApplyInFnSet left) (matrixApplyInFnSet right)
  intro i hi
  have hi' := ((F.sep_members _ _ _).mp hi).1
  rw [matrixApplyEntryComplex left i hi', matrixApplyEntryComplex right i hi']
  change finiteAggregateValue false (matrixIndexValue n) (fun j =>
      NativeBridge.complexValue (F.callValue (denote ab) (FiniteFunction.pack2 i j)) *
        NativeBridge.complexValue (F.callValue (denote v) j)) =
    finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote bv) s))
  calc
    _ = finiteAggregateValue false (matrixIndexValue n) (fun j =>
        finiteAggregateValue false (matrixIndexValue k) (fun s =>
          NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
            NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 s j))) *
        NativeBridge.complexValue (F.callValue (denote v) j)) := by
      apply finiteAggregateValue_congr
      intro j hj
      exact congrArg (fun z : ℂ => z * NativeBridge.complexValue (F.callValue (denote v) j))
        (matrixMultiplyEntryComplex ab i j hi' hj)
    _ = finiteAggregateValue false (matrixIndexValue k) (fun s =>
        NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) *
          finiteAggregateValue false (matrixIndexValue n) (fun j =>
            NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 s j)) *
              NativeBridge.complexValue (F.callValue (denote v) j))) :=
      finiteSumValueMulAssoc _ _ _ _ _ (matrixIndexFinite k hk) (matrixIndexFinite n hn)
    _ = _ := by
      apply finiteAggregateValue_congr
      intro s hs
      exact congrArg (fun z : ℂ => NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i s)) * z)
        (matrixApplyEntryComplex bv s hs).symm

end Litex


namespace Litex

theorem partialQuotientGraphLaws {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n axis : M.Value)
    (returnsReal : ∀ x, M.mem x (F.domainValue f) → M.mem (F.callValue f x) (M.standard .real))
    (pointDomain : M.mem point (F.domainValue f)) :
    (∀ h, M.mem h (F.domainValue (partialQuotientValue f point n axis)) ↔
      M.mem h (M.standard .real) ∧ h≠M.number 0 ∧
        M.mem (coordinatePathValue point n axis h) (F.domainValue f)) ∧
    (∀ h, M.mem h (F.domainValue (partialQuotientValue f point n axis)) →
      F.callValue (partialQuotientValue f point n axis) h =
        M.divValue (M.subValue (F.callValue f (coordinatePathValue point n axis h))
          (F.callValue f point)) h) := by
  let D := F.sepValue (M.standard .real) (fun h => h≠M.number 0 ∧
    M.mem (coordinatePathValue point n axis h) (F.domainValue f))
  let body := fun h => M.divValue (M.subValue (F.callValue f (coordinatePathValue point n axis h))
    (F.callValue f point)) h
  have ret : ∀ h, M.mem h D → M.mem (body h) (M.standard .real) := by
    intro h hh
    obtain ⟨hh,hn,hpath⟩ := (F.sep_members _ _ _).mp hh
    obtain ⟨r,hr⟩ := (M.real_members _).mp hh
    obtain ⟨a,ha⟩ := (M.real_members _).mp (returnsReal _ hpath)
    obtain ⟨b,hb⟩ := (M.real_members _).mp (returnsReal _ pointDomain)
    have hnC : (r : ℂ)≠0 := by intro eq; apply hn; rw [hr,eq]
    apply (M.real_members _).mpr
    refine ⟨(a-b)/r,?_⟩
    dsimp only [body]
    rw [ha,hb,hr,M.sub_numbers,M.div_numbers _ _ hnC,←Complex.ofReal_sub,←Complex.ofReal_div]
  have member := F.graph_inFnSet D (M.standard .real) body ret
  have domain := F.domainValue_eq (F.sep_isSet _ _ (M.standard_isSet .real)) member
  constructor
  · intro h
    change M.mem h (F.domainValue (F.graphValue D (M.standard .real) body)) ↔ _
    rw [domain]
    exact F.sep_members _ _ _
  · intro h hh
    change F.callValue (F.graphValue D (M.standard .real) body) h=body h
    apply F.call_graphValue D (M.standard .real) body ret h
    change M.mem h (F.domainValue (F.graphValue D (M.standard .real) body)) at hh
    rw [domain] at hh
    exact hh

theorem partialDerivativeCandidatesEqualOnOverlap {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g point n axis value other : M.Value)
    (returnsF : ∀ x, M.mem x (F.domainValue f) → M.mem (F.callValue f x) (M.standard .real))
    (returnsG : ∀ x, M.mem x (F.domainValue g) → M.mem (F.callValue g x) (M.standard .real))
    (pointF : M.mem point (F.domainValue f)) (pointG : M.mem point (F.domainValue g))
    (same : ∀ x, M.mem x (F.domainValue f) → M.mem x (F.domainValue g) → F.callValue f x=F.callValue g x)
    (h : HasPartialDerivativeAtValue M f point n axis value)
    (k : HasPartialDerivativeAtValue M g point n axis other) : value=other := by
  obtain ⟨_,p,r,hp,hr,ha,he⟩ := h
  obtain ⟨hi,q,s,hq,hs,_,hk⟩ := k
  have hp0 : p=0 := Complex.ofReal_injective (M.number_injective (hp.symm.trans (by simp)))
  have hq0 : q=0 := Complex.ofReal_injective (M.number_injective (hq.symm.trans (by simp)))
  subst p q
  obtain ⟨radius,hradius,hnear⟩ := hi
  obtain ⟨rad,hrad,hradpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
  have lawsF := partialQuotientGraphLaws f point n axis returnsF pointF
  have lawsG := partialQuotientGraphLaws g point n axis returnsG pointG
  have equal : r=s := by
    apply finiteFunctionLimitUnique .both (partialQuotientValue f point n axis) 0 r s ha he
    intro epsilon hepsilon
    obtain ⟨delta,hdelta,hcontrol⟩ := hk epsilon hepsilon
    refine ⟨Min.min delta rad,lt_min hdelta hradpos,?_⟩
    intro input hinput hpos hsmall
    have bound : |input|<rad := by
      have := lt_of_lt_of_le hsmall (min_le_right delta rad)
      simpa only [finiteLimitDistance,sub_zero] using this
    have inputG : M.mem (M.number (input : ℂ)) (F.domainValue (partialQuotientValue g point n axis)) := by
      apply (lawsG.1 _).mpr
      refine ⟨(M.real_members _).mpr ⟨input,rfl⟩,(lawsF.1 _).mp hinput |>.2.1,?_⟩
      apply hnear _ ((M.real_members _).mpr ⟨input,rfl⟩)
      rw [absValue_number,hrad]
      exact ⟨|input|,rad,rfl,rfl,bound⟩
    obtain ⟨output,houtput,herror⟩ := hcontrol input inputG hpos (lt_of_lt_of_le hsmall (min_le_left _ _))
    refine ⟨output,?_,herror⟩
    rw [lawsG.2 _ inputG] at houtput
    rw [lawsF.2 _ hinput]
    rw [same _ ((lawsF.1 _).mp hinput).2.2 ((lawsG.1 _).mp inputG).2.2,same point pointF pointG]
    exact houtput
  exact hr.trans ((congrArg (fun z : ℝ => M.number (z : ℂ)) equal).trans hs.symm)

def SecondPartialDefinitionValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f domain point n firstAxis secondAxis value : M.Value) : Prop :=
  ∃ localSet : Obj (M := M) M.Value,
    ∃ (_ : M.mem (denote localSet) (F.powerValue (realVectorSetValue n))),
    ∃ first : Obj (M := M) M.Value,
      ∃ (_ : M.mem (denote first) (F.fnSetValue (F.sepValue (denote localSet) (fun _=>True)) (M.standard .real)))
        (_ : ∀ x, M.mem x (denote localSet) → M.mem x domain)
        (_ : M.mem point (denote localSet))
        (_ : ∀ x, M.mem x (denote localSet) → M.mem x (F.sepValue (denote localSet)
          (fun x => ∃ (_ : M.mem x (denote localSet)),
            HasPartialDerivativeAtValue M f x n firstAxis (F.callValue (denote first) x)))),
      HasPartialDerivativeAtValue M (denote first) point n secondAxis value

def HasSecondPartialAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n firstAxis secondAxis value : M.Value) : Prop :=
  SecondPartialDefinitionValue M f (F.domainValue f) point n firstAxis secondAxis value

theorem secondPartialCandidateReal {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n firstAxis secondAxis value : M.Value)
    (h : HasSecondPartialAtValue M f point n firstAxis secondAxis value) :
    M.mem value (M.standard .real) := by
  obtain ⟨_,_,g,_,_,_,_,hg⟩ := h
  exact partialDerivativeCandidateReal (denote g) point n secondAxis value hg

theorem secondPartialCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n firstAxis secondAxis value other : M.Value)
    (h : HasSecondPartialAtValue M f point n firstAxis secondAxis value)
    (k : HasSecondPartialAtValue M f point n firstAxis secondAxis other) : value=other := by
  obtain ⟨D,_,g,hg,_,hp,hparts,hsecond⟩ := h
  obtain ⟨E,_,j,hj,_,kpoint,kparts,ksecond⟩ := k
  have dg : F.domainValue (denote g) = F.sepValue (denote D) (fun _=>True) :=
    F.domainValue_eq (F.sep_isSet _ _ (by exact D.wd)) hg
  have dj : F.domainValue (denote j) = F.sepValue (denote E) (fun _=>True) :=
    F.domainValue_eq (F.sep_isSet _ _ (by exact E.wd)) hj
  have pg : M.mem point (F.domainValue (denote g)) := by
    rw [dg]
    exact (F.sep_members _ _ _).mpr ⟨hp,True.intro⟩
  have pj : M.mem point (F.domainValue (denote j)) := by
    rw [dj]
    exact (F.sep_members _ _ _).mpr ⟨kpoint,True.intro⟩
  apply partialDerivativeCandidatesEqualOnOverlap (denote g) (denote j) point n secondAxis value other
    (fun x hx => F.call_mem _ _ _ _ hg (by rw [←dg];exact hx))
    (fun x hx => F.call_mem _ _ _ _ hj (by rw [←dj];exact hx)) pg pj _ hsecond ksecond
  intro x hx hy
  rw [dg] at hx
  rw [dj] at hy
  exact partialDerivativeCandidatesEqual f x n firstAxis _ _
    ((F.sep_members _ _ _).mp (hparts x ((F.sep_members _ _ _).mp hx).1)).2.choose_spec
    ((F.sep_members _ _ _).mp (kparts x ((F.sep_members _ _ _).mp hy).1)).2.choose_spec

theorem secondPartialExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n firstAxis secondAxis value : M.Value)
    (h : HasSecondPartialAtValue M f point n firstAxis secondAxis value) :
    ∃ v : Obj (M := M) M.Value, M.mem (denote v) (M.standard .real) ∧
      HasSecondPartialAtValue M f point n firstAxis secondAxis (denote v) := by
  have hv := secondPartialCandidateReal f point n firstAxis secondAxis value h
  exact ⟨semanticObject value (M.member_isSet hv),hv,h⟩

end Litex


namespace Litex

theorem transposeEntryComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ)) (i j : M.Value)
    (hi : M.mem i (matrixIndexValue p.val.cols)) (hj : M.mem j (matrixIndexValue p.val.rows)) :
    NativeBridge.complexValue (F.callValue (denote p) (FiniteFunction.pack2 i j)) =
      NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 j i)) := by
  rw [transposeCall p _ (matrixDomain_pair p.val.cols p.val.rows i j hi hj)]
  simp only [matrixTransposeBody, FiniteFunction.unpack_pack2]

theorem conjugateTransposeEntryComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ)) (i j : M.Value)
    (hi : M.mem i (matrixIndexValue p.val.cols)) (hj : M.mem j (matrixIndexValue p.val.rows)) :
    NativeBridge.complexValue (F.callValue (denote p) (FiniteFunction.pack2 i j)) =
      star (NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 j i))) := by
  rw [conjugateTransposeCall p _ (matrixDomain_pair p.val.cols p.val.rows i j hi hj)]
  simp only [matrixConjugateTransposeBody, matrixTransposeBody, FiniteFunction.unpack_pack2]
  obtain ⟨z, hz⟩ := (M.complex_members _).mp
    (F.call_mem _ _ _ _ p.wd.2.2 (matrixDomain_pair p.val.rows p.val.cols j i hj hi))
  rw [hz, complexUnaryValue_number, NativeBridge.complexValue_number, NativeBridge.complexValue_number]

theorem finiteSumValueStar {M : Semantics.{u}} (A : M.Value)
    (f : M.Value → ℂ) (hA : (memberSet A).Finite) :
    finiteAggregateValue false A (fun k => star (f k)) =
      star (finiteAggregateValue false A f) := by
  classical
  simp only [finiteAggregateValue, dif_pos hA, Bool.false_eq_true, ↓reduceIte]
  exact (map_sum (starRingEnd ℂ) _ _).symm

theorem matrixMultiplyTranspose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m : Obj (M := M) γ)
    (k : Obj (M := M) δ) (n : Obj (M := M) ε)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain k n) (M.standard .complex))) :
    Same (transpose (matrixMultiply a b m k n hm hk hn ha hb) m n hm hn (matrixMultiplyInFnSet _))
      (matrixMultiply (transpose b k n hk hn hb) (transpose a m k hm hk ha) n k m hn hk hm
        (transposeInFnSet _) (transposeInFnSet _)) := by
  let ab := matrixMultiply a b m k n hm hk hn ha hb
  let bt := transpose b k n hk hn hb
  let atr := transpose a m k hm hk ha
  let left := transpose ab m n hm hn (matrixMultiplyInFnSet ab)
  let right := matrixMultiply bt atr n k m hn hk hm (transposeInFnSet bt) (transposeInFnSet atr)
  apply matrixSameOfComplexEntries left right n m (transposeInFnSet left) (matrixMultiplyInFnSet right)
  intro i j hi hj
  rw [transposeEntryComplex left i j hi hj, matrixMultiplyEntryComplex right i j hi hj]
  change NativeBridge.complexValue (F.callValue (denote ab) (FiniteFunction.pack2 j i)) =
    finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote bt) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote atr) (FiniteFunction.pack2 s j)))
  rw [matrixMultiplyEntryComplex ab j i hj hi]
  apply finiteAggregateValue_congr
  intro s hs
  rw [transposeEntryComplex bt i s hi hs, transposeEntryComplex atr s j hs hj]
  exact mul_comm _ _

theorem matrixMultiplyAdjoint {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m : Obj (M := M) γ)
    (k : Obj (M := M) δ) (n : Obj (M := M) ε)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain k n) (M.standard .complex))) :
    Same (conjugateTranspose (matrixMultiply a b m k n hm hk hn ha hb) m n hm hn (matrixMultiplyInFnSet _))
      (matrixMultiply (conjugateTranspose b k n hk hn hb) (conjugateTranspose a m k hm hk ha)
        n k m hn hk hm (conjugateTransposeInFnSet _) (conjugateTransposeInFnSet _)) := by
  let ab := matrixMultiply a b m k n hm hk hn ha hb
  let bh := conjugateTranspose b k n hk hn hb
  let ah := conjugateTranspose a m k hm hk ha
  let left := conjugateTranspose ab m n hm hn (matrixMultiplyInFnSet ab)
  let right := matrixMultiply bh ah n k m hn hk hm (conjugateTransposeInFnSet bh) (conjugateTransposeInFnSet ah)
  apply matrixSameOfComplexEntries left right n m (conjugateTransposeInFnSet left) (matrixMultiplyInFnSet right)
  intro i j hi hj
  rw [conjugateTransposeEntryComplex left i j hi hj, matrixMultiplyEntryComplex right i j hi hj]
  change star (NativeBridge.complexValue (F.callValue (denote ab) (FiniteFunction.pack2 j i))) =
    finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote bh) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote ah) (FiniteFunction.pack2 s j)))
  rw [matrixMultiplyEntryComplex ab j i hj hi]
  change star (finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 j s)) *
        NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 s i)))) =
    finiteAggregateValue false (matrixIndexValue k) (fun s =>
      NativeBridge.complexValue (F.callValue (denote bh) (FiniteFunction.pack2 i s)) *
        NativeBridge.complexValue (F.callValue (denote ah) (FiniteFunction.pack2 s j)))
  rw [← finiteSumValueStar _ _ (matrixIndexFinite k hk)]
  apply finiteAggregateValue_congr
  intro s hs
  rw [conjugateTransposeEntryComplex bh i s hi hs, conjugateTransposeEntryComplex ah s j hs hj]
  exact (map_mul (starRingEnd ℂ) _ _).trans (mul_comm _ _)

/-! Hessians use ordered second partials; symmetry is a separate theorem. -/

def HasHessianAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n value : M.Value) : Prop :=
  M.mem value (realMatrixSetValue n n) ∧
    ∀ row, M.mem row (closedRangeValue (M.number 1) n) →
    ∀ col, M.mem col (closedRangeValue (M.number 1) n) →
      HasSecondPartialAtValue M f point n row col (F.callValue value (FiniteFunction.pack2 row col))

theorem hessianCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value other : M.Value) (h : HasHessianAtValue M f point n value)
    (k : HasHessianAtValue M f point n other) : value=other := by
  apply realMatrixValueExt value other n n h.1 k.1
  intro i j hi hj
  exact secondPartialCandidatesEqual _ _ _ _ _ _ _ (h.2 i hi j hj) (k.2 i hi j hj)

noncomputable def hessianValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasHessianAtValue M f point n value then Classical.choose h else M.number 0

theorem hessianValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) (h : ∃ value, HasHessianAtValue M f point n value) :
    HasHessianAtValue M f point n (hessianValue f point n) := by
  classical
  unfold hessianValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure HessianObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  dimension : Obj (M := M) γ

noncomputable instance hessianRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (HessianObj (M := M) α β γ) where
  wd p := In p.dimension NPos ∧
    RealMultivariableFunctionValue M (denote p.function) (denote p.dimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.dimension)) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    ∃ value : Obj (M := M) M.Value, M.mem (denote value) (realMatrixSetValue (denote p.dimension) (denote p.dimension)) ∧
      HasHessianAtValue M (denote p.function) (denote p.point) (denote p.dimension) (denote value)
  denote p := hessianValue (denote p.function) (denote p.point) (denote p.dimension)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2.2
    exact M.member_isSet (hessianValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem hessianExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n value : M.Value) (h : HasHessianAtValue M f point n value) :
    ∃ v : Obj (M := M) M.Value, M.mem (denote v) (realMatrixSetValue n n) ∧ HasHessianAtValue M f point n (denote v) :=
  ⟨semanticObject value (M.member_isSet h.1),h.1,h⟩

theorem hessianInMatrix {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (HessianObj (M := M) α β γ)) : M.mem (denote p) (realMatrixSetValue (denote p.val.dimension) (denote p.val.dimension)) := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2.2
  exact (hessianValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem hessianEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (HessianObj (M := M) α β γ)) (value : M.Value)
    (h : HasHessianAtValue M (denote p.val.function) (denote p.val.point) (denote p.val.dimension) value) :
    denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2.2
  exact hessianCandidatesEqual _ _ _ _ _ (hessianValueSelected _ _ _ ⟨denote v,hc⟩) h

/-! The Laplacian is the sum of diagonal second partials. -/

def HasLaplacianAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n value : M.Value) : Prop :=
  M.mem value (M.standard .real) ∧ ∃ diagonal : Obj (M := M) M.Value,
    M.mem (denote diagonal) (realVectorSetValue n) ∧
    (∀ k, M.mem k (closedRangeValue (M.number 1) n) →
      HasSecondPartialAtValue M f point n k k (F.callValue (denote diagonal) k)) ∧
    vectorSumValue (denote diagonal) n = value

theorem laplacianCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value other : M.Value) (h : HasLaplacianAtValue M f point n value)
    (k : HasLaplacianAtValue M f point n other) : value=other := by
  obtain ⟨_,a,ha,hparts,hsum⟩ := h
  obtain ⟨_,b,hb,kparts,ksum⟩ := k
  have hab : denote a=denote b := realVectorValueExt _ _ n ha hb (by
    intro i hi
    exact secondPartialCandidatesEqual _ _ _ _ _ _ _ (hparts i hi) (kparts i hi))
  exact hsum.symm.trans ((congrArg (fun v => vectorSumValue v n) hab).trans ksum)

noncomputable def laplacianValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasLaplacianAtValue M f point n value then Classical.choose h else M.number 0

theorem laplacianValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) (h : ∃ value, HasLaplacianAtValue M f point n value) :
    HasLaplacianAtValue M f point n (laplacianValue f point n) := by
  classical
  unfold laplacianValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure LaplacianObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  dimension : Obj (M := M) γ

noncomputable instance laplacianRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (LaplacianObj (M := M) α β γ) where
  wd p := In p.dimension NPos ∧
    RealMultivariableFunctionValue M (denote p.function) (denote p.dimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.dimension)) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    ∃ value : Obj (M := M) M.Value, In value R ∧
      HasLaplacianAtValue M (denote p.function) (denote p.point) (denote p.dimension) (denote value)
  denote p := laplacianValue (denote p.function) (denote p.point) (denote p.dimension)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2.2
    exact M.member_isSet (laplacianValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem laplacianExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n value : M.Value) (h : HasLaplacianAtValue M f point n value) :
    ∃ v : Obj (M := M) M.Value, In v R ∧ HasLaplacianAtValue M f point n (denote v) :=
  ⟨semanticObject value (M.member_isSet h.1),h.1,h⟩

theorem laplacianInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (LaplacianObj (M := M) α β γ)) : In p R := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2.2
  exact (laplacianValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem laplacianEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (LaplacianObj (M := M) α β γ)) (value : M.Value)
    (h : HasLaplacianAtValue M (denote p.val.function) (denote p.val.point) (denote p.val.dimension) value) :
    denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2.2
  exact laplacianCandidatesEqual _ _ _ _ _ (laplacianValueSelected _ _ _ ⟨denote v,hc⟩) h

/-! Scalar differentials retain interior and punctured remainder conditions. -/

section DifferentialGeometry
variable {M : Semantics.{u}} [F : FunctionSemantics M]

omit F in
theorem addValuesInReal {a b : M.Value}
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real)) :
    M.mem (M.addValue a b) (M.standard .real) := by
  obtain ⟨r,rfl⟩ := (M.real_members _).mp ha
  obtain ⟨s,rfl⟩ := (M.real_members _).mp hb
  rw [M.add_numbers,←Complex.ofReal_add]
  exact (M.real_members _).mpr ⟨r+s,rfl⟩

omit F in
theorem subValuesInReal {a b : M.Value}
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real)) :
    M.mem (M.subValue a b) (M.standard .real) := by
  obtain ⟨r,rfl⟩ := (M.real_members _).mp ha
  obtain ⟨s,rfl⟩ := (M.real_members _).mp hb
  rw [M.sub_numbers,←Complex.ofReal_sub]
  exact (M.real_members _).mpr ⟨r-s,rfl⟩

theorem identityMatrixValueCall (n row col : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hr : M.mem row (closedRangeValue (M.number 1) n))
    (hc : M.mem col (closedRangeValue (M.number 1) n)) :
    F.callValue (identityMatrixValue n) (FiniteFunction.pack2 row col) = matrixIdentityEntry row col := by
  let length := semanticObject n (M.member_isSet hn)
  have hp := matrixDomain_pair length length row col hr hc
  exact (F.call_graphValue _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _) _ hp).trans
    (by simp only [FiniteFunction.unpack_pack2])

theorem coordinatePathValueBodyReal (point n coordinate displacement index : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem coordinate (closedRangeValue (M.number 1) n))
    (hh : M.mem displacement (M.standard .real))
    (hi : M.mem index (F.sepValue (closedRangeValue (M.number 1) n) (fun _ => True))) :
    M.mem (M.addValue (F.callValue point index) (M.mulValue displacement
      (F.callValue (identityMatrixValue n) (FiniteFunction.pack2 index coordinate)))) (M.standard .real) := by
  rw [identityMatrixValueCall n index coordinate hn ((F.sep_members _ _ _).mp hi).1 hk]
  exact addValuesInReal (F.call_mem _ _ _ _ hp hi) (mulValuesInReal hh (matrixIdentityEntry_inReal _ _))

theorem coordinatePathValueInVector (point n coordinate displacement : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem coordinate (closedRangeValue (M.number 1) n))
    (hh : M.mem displacement (M.standard .real)) :
    M.mem (coordinatePathValue point n coordinate displacement) (realVectorSetValue n) :=
  F.graph_inFnSet _ _ _ (fun i hi => coordinatePathValueBodyReal point n coordinate displacement i hn hp hk hh hi)

theorem coordinatePathValueCall (point n coordinate displacement index : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem coordinate (closedRangeValue (M.number 1) n))
    (hh : M.mem displacement (M.standard .real))
    (hi : M.mem index (closedRangeValue (M.number 1) n)) :
    F.callValue (coordinatePathValue point n coordinate displacement) index =
      M.addValue (F.callValue point index) (M.mulValue displacement (matrixIdentityEntry index coordinate)) := by
  rw [coordinatePathValue, F.call_graphValue _ _ _
    (fun i h => coordinatePathValueBodyReal point n coordinate displacement i hn hp hk hh h)
    _ ((F.sep_members _ _ _).mpr ⟨hi,True.intro⟩)]
  rw [identityMatrixValueCall n index coordinate hn hi hk]

theorem multivariableDifferenceCall (a b n index : M.Value)
    (ha : M.mem a (realVectorSetValue n)) (hb : M.mem b (realVectorSetValue n))
    (hi : M.mem index (closedRangeValue (M.number 1) n)) :
    F.callValue (multivariableDifferenceValue a b n) index = M.subValue (F.callValue a index) (F.callValue b index) := by
  exact F.call_graphValue _ _ _ (fun k hk => subValuesInReal
    (F.call_mem _ _ _ _ ha hk) (F.call_mem _ _ _ _ hb hk)) _ ((F.sep_members _ _ _).mpr ⟨hi,True.intro⟩)

noncomputable local instance : DecidableEq M.Value := Classical.decEq _

theorem coordinatePathDifferenceCall (point n coordinate index : M.Value) (h : ℝ)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem coordinate (closedRangeValue (M.number 1) n))
    (hi : M.mem index (closedRangeValue (M.number 1) n)) :
    F.callValue (multivariableDifferenceValue (coordinatePathValue point n coordinate (M.number (h : ℂ))) point n) index =
      if index=coordinate then M.number (h : ℂ) else M.number 0 := by
  classical
  have hh : M.mem (M.number (h : ℂ)) (M.standard .real) := (M.real_members _).mpr ⟨h,rfl⟩
  rw [multivariableDifferenceCall _ _ _ _ (coordinatePathValueInVector point n coordinate _ hn hp hk hh) hp hi,
    coordinatePathValueCall point n coordinate _ index hn hp hk hh hi]
  obtain ⟨x,hx⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hp ((F.sep_members _ _ _).mpr ⟨hi,True.intro⟩))
  by_cases eq : index=coordinate
  · rw [if_pos eq,eq,matrixIdentityEntrySelf,←eq,hx,M.mul_numbers,M.add_numbers,M.sub_numbers]
    congr 1
    ring
  · rw [if_neg eq,matrixIdentityEntryDifferent _ _ eq,hx,M.mul_numbers,M.add_numbers,M.sub_numbers]
    congr 1
    ring

theorem coordinatePathDistance (point n coordinate : M.Value) (h : ℝ)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem coordinate (closedRangeValue (M.number 1) n)) :
    multivariableDistanceValue (coordinatePathValue point n coordinate (M.number (h : ℂ))) point n =
      M.number ((|h| : ℝ) : ℂ) := by
  let length := semanticObject n (M.member_isSet hn)
  have finiteIndices : (memberSet (closedRangeValue (M.number 1) n)).Finite := matrixIndexFinite length hn
  unfold multivariableDistanceValue
  have same := finiteAggregateValue_congr (M := M) false (closedRangeValue (M.number 1) n)
    (fun k => ((‖NativeBridge.complexValue (F.callValue
      (multivariableDifferenceValue (coordinatePathValue point n coordinate (M.number (h : ℂ))) point n) k)‖ ^ 2 : ℝ) : ℂ))
    (fun k => if k=coordinate then ((h^2 : ℝ) : ℂ) else 0) (by
      intro k hk'
      rw [coordinatePathDifferenceCall point n coordinate k h hn hp hk hk']
      by_cases eq : k=coordinate
      · rw [if_pos eq,if_pos eq,NativeBridge.complexValue_number]
        simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
      · rw [if_neg eq,if_neg eq,NativeBridge.complexValue_number]
        norm_num)
  rw [same,finiteSumValueSingle _ (fun _ => ((h^2 : ℝ) : ℂ)) finiteIndices coordinate hk,sqrtValue_number,Real.sqrt_sq_eq_abs]

noncomputable def matrixApplyValue (a b m n : M.Value) : M.Value :=
  F.graphValue (F.sepValue (closedRangeValue (M.number 1) m) (fun _ => True)) (M.standard .complex)
    (fun row => M.number (finiteAggregateValue false (closedRangeValue (M.number 1) n)
      (fun k => NativeBridge.complexValue (F.callValue
        (F.graphValue (F.sepValue (closedRangeValue (M.number 1) n) (fun _ => True))
          (M.standard .complex) (matrixApplyTerm a b row)) k))))

theorem matrixApplyValueRow (a b m n row : M.Value)
    (hm : M.isSet m) (hn : M.isSet n)
    (ha : M.mem a (realMatrixSetValue m n)) (hb : M.mem b (realVectorSetValue n))
    (hr : M.mem row (closedRangeValue (M.number 1) m)) :
    F.callValue (matrixApplyValue a b m n) row =
      M.number (finiteAggregateValue false (closedRangeValue (M.number 1) n)
        (fun k => NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 row k)) *
          NativeBridge.complexValue (F.callValue b k))) := by
  let rows := semanticObject m hm
  let cols := semanticObject n hn
  rw [matrixApplyValue,F.call_graphValue _ _ _
    (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩) _ ((F.sep_members _ _ _).mpr ⟨hr,True.intro⟩)]
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro k hk
  have realEntry : ∀ j, M.mem j (F.sepValue (closedRangeValue (M.number 1) n) (fun _ => True)) →
      M.mem (matrixApplyTerm a b row j) (M.standard .real) := by
    intro j hj
    exact mulValuesInReal (F.call_mem _ _ _ _ ha
      (matrixDomain_pair rows cols row j hr ((F.sep_members _ _ _).mp hj).1)) (F.call_mem _ _ _ _ hb hj)
  rw [F.call_graphValue _ _ _ (fun j hj => M.real_subset_complex _ (realEntry j hj)) _ ((F.sep_members _ _ _).mpr ⟨hk,True.intro⟩)]
  obtain ⟨x,hx⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ ha (matrixDomain_pair rows cols row k hr hk))
  obtain ⟨y,hy⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hb ((F.sep_members _ _ _).mpr ⟨hk,True.intro⟩))
  simp only [matrixApplyTerm,hx,hy,M.mul_numbers,NativeBridge.complexValue_number]

theorem matrixApplyCoordinatePath (a point m n row coordinate : M.Value) (h : ℝ)
    (hm : M.isSet m) (hn : M.mem n (M.standard .natural))
    (ha : M.mem a (realMatrixSetValue m n)) (hp : M.mem point (realVectorSetValue n))
    (hr : M.mem row (closedRangeValue (M.number 1) m))
    (hk : M.mem coordinate (closedRangeValue (M.number 1) n)) :
    F.callValue (matrixApplyValue a
      (multivariableDifferenceValue (coordinatePathValue point n coordinate (M.number (h : ℂ))) point n) m n) row =
      M.mulValue (F.callValue a (FiniteFunction.pack2 row coordinate)) (M.number (h : ℂ)) := by
  have hh : M.mem (M.number (h : ℂ)) (M.standard .real) := (M.real_members _).mpr ⟨h,rfl⟩
  have pathMem := coordinatePathValueInVector point n coordinate _ hn hp hk hh
  have differenceMem : M.mem (multivariableDifferenceValue (coordinatePathValue point n coordinate (M.number (h : ℂ))) point n) (realVectorSetValue n) :=
    F.graph_inFnSet _ _ _ (fun k hk => subValuesInReal (F.call_mem _ _ _ _ pathMem hk) (F.call_mem _ _ _ _ hp hk))
  rw [matrixApplyValueRow _ _ _ _ _ hm (M.member_isSet hn) ha differenceMem hr]
  let rows := semanticObject m hm
  let cols := semanticObject n (M.member_isSet hn)
  have finiteIndices : (memberSet (closedRangeValue (M.number 1) n)).Finite := matrixIndexFinite cols hn
  have same := finiteAggregateValue_congr (M := M) false (closedRangeValue (M.number 1) n)
    (fun k => NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 row k)) *
      NativeBridge.complexValue (F.callValue
        (multivariableDifferenceValue (coordinatePathValue point n coordinate (M.number (h : ℂ))) point n) k))
    (fun k => if k=coordinate then NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 row k)) * (h : ℂ) else 0) (by
      intro k hki
      rw [coordinatePathDifferenceCall point n coordinate k h hn hp hk hki]
      by_cases eq : k=coordinate
      · simp only [if_pos eq,NativeBridge.complexValue_number]
      · simp only [if_neg eq,NativeBridge.complexValue_number,mul_zero])
  rw [same,finiteSumValueSingle _ (fun k => NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 row k)) * (h : ℂ)) finiteIndices coordinate hk]
  obtain ⟨x,hx⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ ha (matrixDomain_pair rows cols row coordinate hr hk))
  rw [hx,M.mul_numbers,NativeBridge.complexValue_number]

def MultivariableInteriorValue (domain point n : M.Value) : Prop :=
  ∃ radius : Obj (M := M) M.Value, In radius RPos ∧
    ∀ input, M.mem input (realVectorSetValue n) →
      RealLtValue M (multivariableDistanceValue input point n) (denote radius) → M.mem input domain

noncomputable def scalarDifferentialErrorValue (f point n matrix input : M.Value) : M.Value :=
  absValue (M.subValue (M.subValue (F.callValue f input) (F.callValue f point))
    (F.callValue (matrixApplyValue matrix (multivariableDifferenceValue input point n) (M.number 1) n) (M.number 1)))

def ScalarDifferentialRemainderValue (f point n matrix : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ delta : Obj (M := M) M.Value, In delta RPos ∧
      ∀ input, M.mem input (F.domainValue f) →
        RealLtValue M (M.number 0) (multivariableDistanceValue input point n) →
        RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
        RealLtValue M (scalarDifferentialErrorValue f point n matrix input)
          (M.mulValue epsilon (multivariableDistanceValue input point n))

def HasScalarDifferentialAtValue (M : Semantics.{u}) [F : FunctionSemantics M] (f point n matrix : M.Value) : Prop :=
  M.mem matrix (realMatrixSetValue (M.number 1) n) ∧
    MultivariableInteriorValue (F.domainValue f) point n ∧ ScalarDifferentialRemainderValue f point n matrix

theorem scalarDifferentialErrorCoordinate (f point n matrix coordinate : M.Value) (h y z a : ℝ)
    (hn : M.mem n (M.standard .natural)) (hp : M.mem point (realVectorSetValue n))
    (hm : M.mem matrix (realMatrixSetValue (M.number 1) n))
    (hk : M.mem coordinate (closedRangeValue (M.number 1) n))
    (hy : F.callValue f (coordinatePathValue point n coordinate (M.number (h : ℂ)))=M.number (y : ℂ))
    (hz : F.callValue f point=M.number (z : ℂ))
    (ha : F.callValue matrix (FiniteFunction.pack2 (M.number 1) coordinate)=M.number (a : ℂ)) :
    scalarDifferentialErrorValue f point n matrix (coordinatePathValue point n coordinate (M.number (h : ℂ))) =
      M.number ((|y-z-a*h| : ℝ) : ℂ) := by
  have hr : M.mem (M.number 1) (closedRangeValue (M.number 1) (M.number 1)) := by
    simpa only [Int.cast_one] using (closedRangeValue_members (M := M) 1 1 (M.number 1)).mpr ⟨1,by norm_num,le_rfl,le_rfl⟩
  unfold scalarDifferentialErrorValue
  rw [matrixApplyCoordinatePath _ _ _ _ _ _ _ (M.member_isSet ((M.complex_members _).mpr ⟨1,rfl⟩)) hn hm hp hr hk,
    hy,hz,ha,M.mul_numbers,M.sub_numbers,M.sub_numbers,
    ←Complex.ofReal_mul,←Complex.ofReal_sub,←Complex.ofReal_sub,absValue_number]

theorem scalarDifferentialCandidatesEqual (f point n matrix other : M.Value)
    (hn : M.mem n (M.standard .natural)) (hp : M.mem point (realVectorSetValue n))
    (hf : RealMultivariableFunctionValue M f n) (hpoint : M.mem point (F.domainValue f))
    (h : HasScalarDifferentialAtValue M f point n matrix)
    (k : HasScalarDifferentialAtValue M f point n other) : matrix=other := by
  apply realMatrixValueExt matrix other (M.number 1) n h.1 k.1
  intro row coordinate hrow hcoordinate
  obtain ⟨rowZ,rfl,hlo,hhi⟩ := (closedRangeValue_members (M := M) 1 1 row).mp (by simpa only [Int.cast_one] using hrow)
  have rowOne : rowZ=1 := le_antisymm hhi hlo
  subst rowZ
  simp only [Int.cast_one] at *
  let rows := semanticObject (M.number 1) (M.member_isSet ((M.complex_members _).mpr ⟨1,rfl⟩))
  let cols := semanticObject n (M.member_isSet hn)
  have pairMember := matrixDomain_pair rows cols (M.number 1) coordinate hrow hcoordinate
  obtain ⟨a,ha⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ h.1 pairMember)
  obtain ⟨b,hb⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ k.1 pairMember)
  rw [ha,hb]
  suffices a=b by rw [this]
  by_contra hne
  let epsilon : ℝ := |a-b|/3
  have hepsilon : 0<epsilon := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
  have hemem := numberInRPos (M := M) epsilon hepsilon
  obtain ⟨delta,hd,hcontrol⟩ := h.2.2 (M.number (epsilon : ℂ)) hemem
  obtain ⟨eta,he,kcontrol⟩ := k.2.2 (M.number (epsilon : ℂ)) hemem
  obtain ⟨radius,hr,hinterior⟩ := h.2.1
  obtain ⟨dr,hdr,hdrpos⟩ := NativeBridge.realWitnessOfPositive delta (inRPos_positive delta hd)
  obtain ⟨er,her,herpos⟩ := NativeBridge.realWitnessOfPositive eta (inRPos_positive eta he)
  obtain ⟨rr,hrr,hrrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hr)
  let step : ℝ := Min.min rr (Min.min dr er)/2
  have hstep : 0<step := div_pos (lt_min hrrpos (lt_min hdrpos herpos)) (by norm_num)
  have hstepSmall : step<Min.min rr (Min.min dr er) := by dsimp [step]; linarith [lt_min hrrpos (lt_min hdrpos herpos)]
  have hsr : step<rr := lt_of_lt_of_le hstepSmall (min_le_left _ _)
  have hsd : step<dr := lt_of_lt_of_le hstepSmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have hse : step<er := lt_of_lt_of_le hstepSmall (le_trans (min_le_right _ _) (min_le_right _ _))
  let input := coordinatePathValue point n coordinate (M.number (step : ℂ))
  have inputVector : M.mem input (realVectorSetValue n) := coordinatePathValueInVector point n coordinate _ hn hp hcoordinate ((M.real_members _).mpr ⟨step,rfl⟩)
  have distance : multivariableDistanceValue input point n=M.number (step : ℂ) := by
    dsimp only [input]
    rw [coordinatePathDistance point n coordinate step hn hp hcoordinate,abs_of_pos hstep]
  have inDomain := hinterior input inputVector ⟨step,rr,distance,hrr,hsr⟩
  have positive : RealLtValue M (M.number 0) (multivariableDistanceValue input point n) := ⟨0,step,by simp,distance,hstep⟩
  have ca := hcontrol input inDomain positive ⟨step,dr,distance,hdr,hsd⟩
  have cb := kcontrol input inDomain positive ⟨step,er,distance,her,hse⟩
  obtain ⟨y,hy⟩ := (M.real_members _).mp (multivariableFunctionReturnsReal f n input hf inDomain)
  obtain ⟨z,hz⟩ := (M.real_members _).mp (multivariableFunctionReturnsReal f n point hf hpoint)
  rw [scalarDifferentialErrorCoordinate f point n matrix coordinate step y z a hn hp h.1 hcoordinate hy hz ha,
    distance,M.mul_numbers,←Complex.ofReal_mul] at ca
  rw [scalarDifferentialErrorCoordinate f point n other coordinate step y z b hn hp k.1 hcoordinate hy hz hb,
    distance,M.mul_numbers,←Complex.ofReal_mul] at cb
  have ca' := (realLtValue_numbers _ _).mp ca
  have cb' := (realLtValue_numbers _ _).mp cb
  have triangle := abs_sub_le (y-z-b*step) 0 (y-z-a*step)
  have eq : (y-z-b*step)-(y-z-a*step)=(a-b)*step := by ring
  rw [eq,abs_mul,abs_of_pos hstep] at triangle
  simp only [sub_zero,zero_sub,abs_neg] at triangle
  dsimp [epsilon] at ca' cb'
  nlinarith [abs_pos.mpr (sub_ne_zero.mpr hne)]

end DifferentialGeometry

noncomputable def scalarDifferentialValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasScalarDifferentialAtValue M f point n value then Classical.choose h else M.number 0

theorem scalarDifferentialValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) (h : ∃ value, HasScalarDifferentialAtValue M f point n value) :
    HasScalarDifferentialAtValue M f point n (scalarDifferentialValue f point n) := by
  classical
  unfold scalarDifferentialValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure ScalarDifferentialObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  dimension : Obj (M := M) γ

noncomputable instance scalarDifferentialRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (ScalarDifferentialObj (M := M) α β γ) where
  wd p := In p.dimension NPos ∧
    RealMultivariableFunctionValue M (denote p.function) (denote p.dimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.dimension)) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    ∃ value : Obj (M := M) M.Value, M.mem (denote value) (realMatrixSetValue (M.number 1) (denote p.dimension)) ∧
      HasScalarDifferentialAtValue M (denote p.function) (denote p.point) (denote p.dimension) (denote value)
  denote p := scalarDifferentialValue (denote p.function) (denote p.point) (denote p.dimension)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2.2
    exact M.member_isSet (scalarDifferentialValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem scalarDifferentialExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n value : M.Value) (h : HasScalarDifferentialAtValue M f point n value) :
    ∃ v : Obj (M := M) M.Value, M.mem (denote v) (realMatrixSetValue (M.number 1) n) ∧ HasScalarDifferentialAtValue M f point n (denote v) :=
  ⟨semanticObject value (M.member_isSet h.1),h.1,h⟩

theorem scalarDifferentialInMatrix {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (ScalarDifferentialObj (M := M) α β γ)) : M.mem (denote p) (realMatrixSetValue (M.number 1) (denote p.val.dimension)) := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2.2
  exact (scalarDifferentialValueSelected _ _ _ ⟨denote value,hc⟩).1

theorem scalarDifferentialEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (ScalarDifferentialObj (M := M) α β γ)) (value : M.Value)
    (h : HasScalarDifferentialAtValue M (denote p.val.function) (denote p.val.point) (denote p.val.dimension) value) :
    denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2.2
  exact scalarDifferentialCandidatesEqual _ _ _ _ _ (inNPos_natural _ p.wd.1) p.wd.2.2.1 p.wd.2.1 p.wd.2.2.2.1 (scalarDifferentialValueSelected _ _ _ ⟨denote v,hc⟩) h



/-! Total differentials preserve the vector remainder norm. -/

section TotalDifferentialGeometry
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem matrixApplyValueInVector (a b m n : M.Value)
    (hm : M.mem m (M.standard .natural)) (hn : M.mem n (M.standard .natural))
    (ha : M.mem a (realMatrixSetValue m n)) (hb : M.mem b (realVectorSetValue n)) :
    M.mem (matrixApplyValue a b m n) (realVectorSetValue m) := by
  let rows := semanticObject m (M.member_isSet hm)
  let cols := semanticObject n (M.member_isSet hn)
  let matrix := semanticObject a (M.member_isSet ha)
  let vector := semanticObject b (M.member_isSet hb)
  let result := matrixApply matrix vector rows cols hm hn (functionRealToComplex ha) (functionRealToComplex hb)
  exact matrixApplyInRealFnSet result ha hb

noncomputable def totalDifferentialRemainderVectorValue (f point n m matrix input : M.Value) : M.Value :=
  F.graphValue (F.sepValue (closedRangeValue (M.number 1) m) (fun _ => True)) (M.standard .real)
    (fun row => M.subValue (M.subValue (F.callValue (F.callValue f input) row)
      (F.callValue (F.callValue f point) row))
      (F.callValue (matrixApplyValue matrix (multivariableDifferenceValue input point n) m n) row))

noncomputable def totalDifferentialErrorValue (f point n m matrix input : M.Value) : M.Value :=
  sqrtValue (M.number (finiteAggregateValue false (closedRangeValue (M.number 1) m)
    (fun row => ((‖NativeBridge.complexValue (F.callValue (totalDifferentialRemainderVectorValue f point n m matrix input) row)‖ ^ 2 : ℝ) : ℂ))))

def TotalDifferentialRemainderValue (f point n m matrix : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ delta : Obj (M := M) M.Value, In delta RPos ∧
      ∀ input, M.mem input (F.domainValue f) →
        RealLtValue M (M.number 0) (multivariableDistanceValue input point n) →
        RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
        RealLtValue M (totalDifferentialErrorValue f point n m matrix input)
          (M.mulValue epsilon (multivariableDistanceValue input point n))

def HasTotalDifferentialAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n m matrix : M.Value) : Prop :=
  M.mem matrix (realMatrixSetValue m n) ∧
    MultivariableInteriorValue (F.domainValue f) point n ∧ TotalDifferentialRemainderValue f point n m matrix

theorem totalDifferentialErrorCoordinateBound (f point n m matrix row coordinate : M.Value) (step y z a : ℝ)
    (hn : M.mem n (M.standard .natural)) (hm : M.mem m (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n)) (hA : M.mem matrix (realMatrixSetValue m n))
    (hrow : M.mem row (closedRangeValue (M.number 1) m))
    (hk : M.mem coordinate (closedRangeValue (M.number 1) n))
    (hinput : M.mem (F.callValue f (coordinatePathValue point n coordinate (M.number (step : ℂ)))) (realVectorSetValue m))
    (hpoint : M.mem (F.callValue f point) (realVectorSetValue m))
    (hy : F.callValue (F.callValue f (coordinatePathValue point n coordinate (M.number (step : ℂ)))) row=M.number (y : ℂ))
    (hz : F.callValue (F.callValue f point) row=M.number (z : ℂ))
    (ha : F.callValue matrix (FiniteFunction.pack2 row coordinate)=M.number (a : ℂ)) :
    ∃ error : ℝ, totalDifferentialErrorValue f point n m matrix (coordinatePathValue point n coordinate (M.number (step : ℂ)))=M.number (error : ℂ) ∧ |y-z-a*step|≤error := by
  let input := coordinatePathValue point n coordinate (M.number (step : ℂ))
  let D := F.sepValue (closedRangeValue (M.number 1) m) (fun _ => True)
  have inputVector := coordinatePathValueInVector point n coordinate _ hn hp hk ((M.real_members _).mpr ⟨step,rfl⟩)
  have difference : M.mem (multivariableDifferenceValue input point n) (realVectorSetValue n) :=
    F.graph_inFnSet _ _ _ (fun k hk => subValuesInReal (F.call_mem _ _ _ _ inputVector hk) (F.call_mem _ _ _ _ hp hk))
  have linear := matrixApplyValueInVector matrix _ m n hm hn hA difference
  have returns : ∀ k, M.mem k D → M.mem (M.subValue (M.subValue
      (F.callValue (F.callValue f input) k) (F.callValue (F.callValue f point) k))
      (F.callValue (matrixApplyValue matrix (multivariableDifferenceValue input point n) m n) k)) (M.standard .real) := by
    intro k hki
    exact subValuesInReal (subValuesInReal (F.call_mem _ _ _ _ hinput hki) (F.call_mem _ _ _ _ hpoint hki)) (F.call_mem _ _ _ _ linear hki)
  let g := fun k => NativeBridge.complexValue (F.callValue (totalDifferentialRemainderVectorValue f point n m matrix input) k)
  have hg : g row=((y-z-a*step : ℝ) : ℂ) := by
    dsimp only [g,totalDifferentialRemainderVectorValue]
    rw [F.call_graphValue _ _ _ returns _ ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩)]
    rw [matrixApplyCoordinatePath _ _ _ _ _ _ _ (M.member_isSet hm) hn hA hp hrow hk,hy,hz,ha,M.mul_numbers,M.sub_numbers,M.sub_numbers,NativeBridge.complexValue_number]
    push_cast
    rfl
  let rows := semanticObject m (M.member_isSet hm)
  have finiteIndices : (memberSet (closedRangeValue (M.number 1) m)).Finite := matrixIndexFinite rows hm
  obtain ⟨sum,_,hsum,hbound⟩ := finiteMagnitudeCoordinateBound _ g finiteIndices row hrow
  refine ⟨Real.sqrt sum,?_,?_⟩
  · unfold totalDifferentialErrorValue
    rw [hsum,sqrtValue_number]
  · simpa only [hg,Complex.norm_real,Real.norm_eq_abs] using hbound

theorem totalDifferentialCandidatesEqual (f point n m matrix other : M.Value)
    (hn : M.mem n (M.standard .natural)) (hm : M.mem m (M.standard .natural)) (hp : M.mem point (realVectorSetValue n))
    (hf : VectorMultivariableFunctionValue M f n m) (hpoint : M.mem point (F.domainValue f))
    (h : HasTotalDifferentialAtValue M f point n m matrix)
    (k : HasTotalDifferentialAtValue M f point n m other) : matrix=other := by
  apply realMatrixValueExt matrix other m n h.1 k.1
  intro row coordinate hrow hcoordinate
  let rows := semanticObject m (M.member_isSet hm)
  let cols := semanticObject n (M.member_isSet hn)
  have pairMember := matrixDomain_pair rows cols row coordinate hrow hcoordinate
  obtain ⟨a,ha⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ h.1 pairMember)
  obtain ⟨b,hb⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ k.1 pairMember)
  rw [ha,hb]
  suffices a=b by rw [this]
  by_contra hne
  let epsilon : ℝ := |a-b|/3
  have hepsilon : 0<epsilon := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
  have hemem := numberInRPos (M := M) epsilon hepsilon
  obtain ⟨delta,hd,hcontrol⟩ := h.2.2 (M.number (epsilon : ℂ)) hemem
  obtain ⟨eta,he,kcontrol⟩ := k.2.2 (M.number (epsilon : ℂ)) hemem
  obtain ⟨radius,hr,hinterior⟩ := h.2.1
  obtain ⟨dr,hdr,hdrpos⟩ := NativeBridge.realWitnessOfPositive delta (inRPos_positive delta hd)
  obtain ⟨er,her,herpos⟩ := NativeBridge.realWitnessOfPositive eta (inRPos_positive eta he)
  obtain ⟨rr,hrr,hrrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hr)
  let step : ℝ := Min.min rr (Min.min dr er)/2
  have hstep : 0<step := div_pos (lt_min hrrpos (lt_min hdrpos herpos)) (by norm_num)
  have hstepSmall : step<Min.min rr (Min.min dr er) := by dsimp [step]; linarith [lt_min hrrpos (lt_min hdrpos herpos)]
  have hsr : step<rr := lt_of_lt_of_le hstepSmall (min_le_left _ _)
  have hsd : step<dr := lt_of_lt_of_le hstepSmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have hse : step<er := lt_of_lt_of_le hstepSmall (le_trans (min_le_right _ _) (min_le_right _ _))
  let input := coordinatePathValue point n coordinate (M.number (step : ℂ))
  have inputVector : M.mem input (realVectorSetValue n) := coordinatePathValueInVector point n coordinate _ hn hp hcoordinate ((M.real_members _).mpr ⟨step,rfl⟩)
  have distance : multivariableDistanceValue input point n=M.number (step : ℂ) := by
    dsimp only [input]
    rw [coordinatePathDistance point n coordinate step hn hp hcoordinate,abs_of_pos hstep]
  have inDomain := hinterior input inputVector ⟨step,rr,distance,hrr,hsr⟩
  have positive : RealLtValue M (M.number 0) (multivariableDistanceValue input point n) := ⟨0,step,by simp,distance,hstep⟩
  have ca := hcontrol input inDomain positive ⟨step,dr,distance,hdr,hsd⟩
  have cb := kcontrol input inDomain positive ⟨step,er,distance,her,hse⟩
  have hinput := multivariableVectorFunctionReturns f n m input hf inDomain
  have hpointValue := multivariableVectorFunctionReturns f n m point hf hpoint
  have rowMember : M.mem row (F.sepValue (closedRangeValue (M.number 1) m) (fun _ => True)) := (F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩
  obtain ⟨y,hy⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hinput rowMember)
  obtain ⟨z,hz⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hpointValue rowMember)
  obtain ⟨ea,hea,habs_a⟩ := totalDifferentialErrorCoordinateBound f point n m matrix row coordinate step y z a hn hm hp h.1 hrow hcoordinate hinput hpointValue hy hz ha
  obtain ⟨eb,heb,habs_b⟩ := totalDifferentialErrorCoordinateBound f point n m other row coordinate step y z b hn hm hp k.1 hrow hcoordinate hinput hpointValue hy hz hb
  rw [hea,distance,M.mul_numbers,←Complex.ofReal_mul] at ca
  rw [heb,distance,M.mul_numbers,←Complex.ofReal_mul] at cb
  have ca' := (realLtValue_numbers _ _).mp ca
  have cb' := (realLtValue_numbers _ _).mp cb
  have triangle := abs_sub_le (y-z-b*step) 0 (y-z-a*step)
  have eq : (y-z-b*step)-(y-z-a*step)=(a-b)*step := by ring
  rw [eq,abs_mul,abs_of_pos hstep] at triangle
  simp only [sub_zero,zero_sub,abs_neg] at triangle
  dsimp [epsilon] at ca' cb'
  nlinarith [abs_pos.mpr (sub_ne_zero.mpr hne)]

end TotalDifferentialGeometry
noncomputable def totalDifferentialValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m : M.Value) : M.Value := by
  classical
  exact if h : ∃ value, HasTotalDifferentialAtValue M f point n m value then Classical.choose h else M.number 0

theorem totalDifferentialValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m : M.Value) (h : ∃ value, HasTotalDifferentialAtValue M f point n m value) :
    HasTotalDifferentialAtValue M f point n m (totalDifferentialValue f point n m) := by
  classical
  unfold totalDifferentialValue
  rw [dif_pos h]
  exact Classical.choose_spec h

structure TotalDifferentialObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x) (δ : Type y)
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] where
  function : Obj (M := M) α
  point : Obj (M := M) β
  inputDimension : Obj (M := M) γ
  outputDimension : Obj (M := M) δ

noncomputable instance totalDifferentialRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (TotalDifferentialObj (M := M) α β γ δ) where
  wd p := In p.inputDimension NPos ∧ In p.outputDimension NPos ∧
    VectorMultivariableFunctionValue M (denote p.function) (denote p.inputDimension) (denote p.outputDimension) ∧
    M.mem (denote p.point) (realVectorSetValue (denote p.inputDimension)) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    ∃ value : Obj (M := M) M.Value,
      M.mem (denote value) (realMatrixSetValue (denote p.outputDimension) (denote p.inputDimension)) ∧
      HasTotalDifferentialAtValue M (denote p.function) (denote p.point)
        (denote p.inputDimension) (denote p.outputDimension) (denote value)
  denote p := totalDifferentialValue (denote p.function) (denote p.point)
    (denote p.inputDimension) (denote p.outputDimension)
  wd_isSet {p} h := by
    obtain ⟨value,_,hc⟩ := h.2.2.2.2.2
    exact M.member_isSet (totalDifferentialValueSelected _ _ _ _ ⟨denote value,hc⟩).1

theorem totalDifferentialExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m value : M.Value) (h : HasTotalDifferentialAtValue M f point n m value) :
    ∃ v : Obj (M := M) M.Value, M.mem (denote v) (realMatrixSetValue m n) ∧
      HasTotalDifferentialAtValue M f point n m (denote v) := ⟨semanticObject value (M.member_isSet h.1),h.1,h⟩

theorem totalDifferentialInMatrix {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (TotalDifferentialObj (M := M) α β γ δ)) :
    M.mem (denote p) (realMatrixSetValue (denote p.val.outputDimension) (denote p.val.inputDimension)) := by
  obtain ⟨value,_,hc⟩ := p.wd.2.2.2.2.2
  exact (totalDifferentialValueSelected _ _ _ _ ⟨denote value,hc⟩).1

theorem totalDifferentialEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (TotalDifferentialObj (M := M) α β γ δ)) (value : M.Value)
    (h : HasTotalDifferentialAtValue M (denote p.val.function) (denote p.val.point)
      (denote p.val.inputDimension) (denote p.val.outputDimension) value) : denote p=value := by
  obtain ⟨v,_,hc⟩ := p.wd.2.2.2.2.2
  exact totalDifferentialCandidatesEqual _ _ _ _ _ _ (inNPos_natural _ p.wd.1) (inNPos_natural _ p.wd.2.1) p.wd.2.2.2.1 p.wd.2.2.1 p.wd.2.2.2.2.1 (totalDifferentialValueSelected _ _ _ _ ⟨denote v,hc⟩) h


end Litex

namespace Litex

theorem matrixPowerValueAdd {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (p q : ℕ) :
    matrixPowerValue (denote a) n (p + q) =
      F.graphValue (matrixDomain n n) (M.standard .complex)
        (matrixMultiplyBody (matrixPowerValue (denote a) n p)
          (matrixPowerValue (denote a) n q) n) := by
  let ap := semanticObject (matrixPowerValue (denote a) n p)
    (M.member_isSet (matrixPowerValue_inFnSet (denote a) n p))
  have hp : M.mem (denote ap) (F.fnSetValue (matrixDomain n n) (M.standard .complex)) :=
    matrixPowerValue_inFnSet (denote a) n p
  induction q with
  | zero =>
    exact (matrixMultiplyIdentityRight ap n n hn hn hp).symm
  | succ q ih =>
    let aq := semanticObject (matrixPowerValue (denote a) n q)
      (M.member_isSet (matrixPowerValue_inFnSet (denote a) n q))
    have hq : M.mem (denote aq) (F.fnSetValue (matrixDomain n n) (M.standard .complex)) :=
      matrixPowerValue_inFnSet (denote a) n q
    have step := congrArg (fun value =>
      F.graphValue (matrixDomain n n) (M.standard .complex)
        (matrixMultiplyBody value (denote a) n)) ih
    exact step.trans (matrixMultiplyAssociative ap aq a n n n n hn hn hn hn hp hq ha)

theorem matrixPowerAdd {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (n : Obj (M := M) β)
    (p : Obj (M := M) γ) (q : Obj (M := M) δ)
    (hn : In n N) (hp : In p N) (hq : In q N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    matrixPowerValue (denote a) n
        (NativeBridge.naturalValue (M.addValue (denote p) (denote q))) =
      F.graphValue (matrixDomain n n) (M.standard .complex)
        (matrixMultiplyBody
          (matrixPowerValue (denote a) n (NativeBridge.naturalValue (denote p)))
          (matrixPowerValue (denote a) n (NativeBridge.naturalValue (denote q))) n) := by
  have hsum : NativeBridge.naturalValue (M.addValue (denote p) (denote q)) =
      NativeBridge.naturalValue (denote p) + NativeBridge.naturalValue (denote q) := by
    conv_lhs => rw [NativeBridge.naturalValue_spec (denote p) hp,
      NativeBridge.naturalValue_spec (denote q) hq, M.add_numbers]
    have h := NativeBridge.naturalValue_number (M := M)
      (NativeBridge.naturalValue (denote p) + NativeBridge.naturalValue (denote q))
    simpa only [Nat.cast_add] using h
  rw [hsum]
  exact matrixPowerValueAdd a n hn ha _ _

end Litex

namespace Litex

theorem matrixScaleEntryComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ)) (i j : M.Value)
    (hi : M.mem i (matrixIndexValue p.val.rows)) (hj : M.mem j (matrixIndexValue p.val.cols)) :
    NativeBridge.complexValue (F.callValue (denote p) (FiniteFunction.pack2 i j)) =
      NativeBridge.complexValue (denote p.val.scalar) *
        NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 i j)) := by
  rw [matrixScaleCall p _ (matrixDomain_pair p.val.rows p.val.cols i j hi hj)]
  simp only [matrixScaleBody, FiniteFunction.unpack_pack2]
  obtain ⟨z, hz⟩ := (M.complex_members _).mp p.wd.1
  obtain ⟨a, ha⟩ := (M.complex_members _).mp
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_pair p.val.rows p.val.cols i j hi hj))
  rw [hz, ha, M.mul_numbers, NativeBridge.complexValue_number,
    NativeBridge.complexValue_number, NativeBridge.complexValue_number]

theorem frobeniusNormSumScale {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ)) :
    frobeniusNormSum (denote p) p.val.rows p.val.cols =
      ((‖NativeBridge.complexValue (denote p.val.scalar)‖ ^ 2 : ℝ) : ℂ) *
        frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols := by
  unfold frobeniusNormSum
  calc
    _ = finiteAggregateValue false (matrixIndexValue p.val.rows) (fun i =>
        finiteAggregateValue false (matrixIndexValue p.val.cols) (fun j =>
          ((‖NativeBridge.complexValue (denote p.val.scalar)‖ ^ 2 : ℝ) : ℂ) *
            ((‖NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 i j))‖ ^ 2 : ℝ) : ℂ))) := by
      apply finiteAggregateValue_congr
      intro i hi
      apply finiteAggregateValue_congr
      intro j hj
      rw [matrixScaleEntryComplex p i j hi hj, norm_mul, mul_pow, Complex.ofReal_mul]
    _ = finiteAggregateValue false (matrixIndexValue p.val.rows) (fun i =>
        ((‖NativeBridge.complexValue (denote p.val.scalar)‖ ^ 2 : ℝ) : ℂ) *
          finiteAggregateValue false (matrixIndexValue p.val.cols) (fun j =>
            ((‖NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 i j))‖ ^ 2 : ℝ) : ℂ))) := by
      apply finiteAggregateValue_congr
      intro i _hi
      exact finiteSumValueMulLeft _ _ _ (matrixIndexFinite p.val.cols p.wd.2.2.1)
    _ = _ := finiteSumValueMulLeft _ _ _ (matrixIndexFinite p.val.rows p.wd.2.1)

theorem frobeniusNormScale {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (z : Obj (M := M) α) (a : Obj (M := M) β)
    (m : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hz : In z C) (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    denote (frobeniusNorm (matrixScale z a m n hz hm hn ha) m n hm hn (matrixScaleInFnSet _)) =
      M.mulValue (denote (complexAbs z hz)) (denote (frobeniusNorm a m n hm hn ha)) := by
  let scaled := matrixScale z a m n hz hm hn ha
  obtain ⟨r, _hr0, hr⟩ := finiteNestedMagnitudeSquareSumNonnegative
    (matrixIndexValue m) (matrixIndexValue n)
    (fun i j => NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i j)))
    (matrixIndexFinite m hm) (matrixIndexFinite n hn)
  have hsum := frobeniusNormSumScale scaled
  change frobeniusNormSum (denote scaled) m n =
    ((‖NativeBridge.complexValue (denote z)‖ ^ 2 : ℝ) : ℂ) * frobeniusNormSum (denote a) m n at hsum
  have haSum : frobeniusNormSum (denote a) m n = (r : ℂ) := hr
  change sqrtValue (M.number (frobeniusNormSum (denote scaled) m n)) =
    M.mulValue (denote (complexAbs z hz)) (sqrtValue (M.number (frobeniusNormSum (denote a) m n)))
  rw [hsum, haSum, ← Complex.ofReal_mul, sqrtValue_number,
    denoteComplexAbs (complexAbs z hz) (NativeBridge.complexValue (denote z))
      (NativeBridge.complexValue_spec (denote z) hz),
    sqrtValue_number, M.mul_numbers]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Complex.ofReal_mul]

universe t

theorem matrixIndexExistsFin {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N)
    (value : M.Value) (hv : M.mem value (matrixIndexValue n)) :
    ∃ i : Fin (NativeBridge.naturalValue (denote n)), value = FiniteFunction.index i := by
  change M.mem value (closedRangeValue (M.number 1) (denote n)) at hv
  have hnValue : denote n = M.number (((NativeBridge.naturalValue (denote n) : ℕ) : ℤ) : ℂ) := by
    simpa only [Int.cast_natCast] using NativeBridge.naturalValue_spec (denote n) hn
  rw [hnValue] at hv
  have hv' : M.mem value (closedRangeValue (M.number ((1 : ℤ) : ℂ))
      (M.number ((NativeBridge.naturalValue (denote n) : ℤ) : ℂ))) := by
    simpa only [Int.cast_one] using hv
  obtain ⟨k, hk, hk1, hkn⟩ := (closedRangeValue_members (M := M) 1
    (NativeBridge.naturalValue (denote n) : ℤ) value).mp hv'
  have hk0 : 0 ≤ k := by omega
  have hkNat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
  let i : Fin (NativeBridge.naturalValue (denote n)) := ⟨k.toNat - 1, by omega⟩
  refine ⟨i, hk.trans ?_⟩
  change M.number (k : ℂ) = M.number ((k.toNat - 1 + 1 : ℕ) : ℂ)
  apply congrArg M.number
  have h : k.toNat - 1 + 1 = k.toNat := by omega
  rw [h]
  exact_mod_cast hkNat.symm

theorem finiteSumMatrixIndex {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N)
    (f : M.Value → ℂ) :
    finiteAggregateValue false (matrixIndexValue n) f =
      ∑ i : Fin (NativeBridge.naturalValue (denote n)), f (FiniteFunction.index i) := by
  classical
  have hf := matrixIndexFinite n hn
  simp only [finiteAggregateValue, dif_pos hf, Bool.false_eq_true, ↓reduceIte]
  symm
  apply Finset.sum_bij (fun i _ => FiniteFunction.index i)
  · intro i _hi
    exact hf.mem_toFinset.mpr (matrixIndexOfFin n hn i)
  · intro i _hi j _hj same
    exact FiniteFunction.index_injective same
  · intro value hv
    obtain ⟨i, hi⟩ := matrixIndexExistsFin n hn value (hf.mem_toFinset.mp hv)
    exact ⟨i, Finset.mem_univ _, hi.symm⟩
  · intro i _hi
    rfl

theorem matrixComplexValueMultiply {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m : Obj (M := M) γ)
    (k : Obj (M := M) δ) (n : Obj (M := M) ε)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain k n) (M.standard .complex))) :
    matrixComplexValue (denote (matrixMultiply a b m k n hm hk hn ha hb)) m n =
      matrixComplexValue (denote a) m k * matrixComplexValue (denote b) k n := by
  ext i j
  change NativeBridge.complexValue (F.callValue
      (denote (matrixMultiply a b m k n hm hk hn ha hb))
      (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j))) = _
  rw [matrixMultiplyEntryComplex _ _ _ (matrixIndexOfFin m hm i) (matrixIndexOfFin n hn j)]
  exact finiteSumMatrixIndex k hk _

theorem matrixSameOfComplexMatrix {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (m : Obj (M := M) γ) (n : Obj (M := M) δ) (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (h : matrixComplexValue (denote a) m n = matrixComplexValue (denote b) m n) : Same a b := by
  apply matrixSameOfComplexEntries a b m n ha hb
  intro i j hi hj
  obtain ⟨row, rfl⟩ := matrixIndexExistsFin m hm i hi
  obtain ⟨col, rfl⟩ := matrixIndexExistsFin n hn j hj
  exact congrFun (congrFun h row) col

theorem matrixDeterminantMultiply {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    matrixDeterminantValue (denote (matrixMultiply a b n n n hn hn hn ha hb)) n =
      M.mulValue (matrixDeterminantValue (denote a) n) (matrixDeterminantValue (denote b) n) := by
  unfold matrixDeterminantValue
  rw [matrixComplexValueMultiply a b n n n hn hn hn ha hb, Matrix.det_mul, M.mul_numbers]

theorem matrixComplexValueScale {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (z : Obj (M := M) α) (a : Obj (M := M) β)
    (m : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hz : In z C) (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    matrixComplexValue (denote (matrixScale z a m n hz hm hn ha)) m n =
      NativeBridge.complexValue (denote z) • matrixComplexValue (denote a) m n := by
  ext i j
  exact matrixScaleEntryComplex (matrixScale z a m n hz hm hn ha) _ _
    (matrixIndexOfFin m hm i) (matrixIndexOfFin n hn j)

theorem matrixMinorShiftIndex {M : Semantics.{u}} (n : ℕ)
    (r : Fin (n+1)) (i : Fin n) :
    matrixMinorShift (M.number ((n+1 : ℕ) : ℂ)) (FiniteFunction.index r)
      (FiniteFunction.index i) = FiniteFunction.index (r.succAbove i) := by
  have h := matrixMinorShift_numbers (M := M) ((n : ℤ)+1) ((r.val : ℤ)+1)
    ((i.val : ℤ)+1) (by omega) (by omega) (by omega) (by omega) (by omega)
  unfold FiniteFunction.index
  by_cases hlt : i.val < r.val
  · have hi : i.castSucc < r := hlt
    rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    rw [if_pos (by omega)] at h
    simpa only [Fin.val_castSucc, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one] using h
  · have hi : r ≤ i.castSucc := Nat.le_of_not_gt hlt
    rw [Fin.succAbove_of_le_castSucc _ _ hi]
    rw [if_neg (by omega)] at h
    simpa only [Fin.val_succ, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one] using h

theorem matrixMinorDomainSucc {M : Semantics.{u}} [F : FunctionSemantics M] (n : ℕ) :
    matrixMinorDomain (number (M := M) ((n+1 : ℕ) : ℂ)) =
      matrixDomain (number (n : ℂ)) (number (n : ℂ)) := by
  have hs : M.subValue (M.number ((n+1 : ℕ) : ℂ)) (M.number 1) = M.number (n : ℂ) := by
    rw [M.sub_numbers]
    congr 1
    push_cast
    ring
  change F.sepValue (FiniteFunction.cartValue ![
    closedRangeValue (M.number 1) (M.subValue (M.number ((n+1 : ℕ) : ℂ)) (M.number 1)),
    closedRangeValue (M.number 1) (M.subValue (M.number ((n+1 : ℕ) : ℂ)) (M.number 1))])
      (fun _ => True) = _
  rw [hs]
  rfl

theorem matrixComplexOnMinorSucc {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (n : ℕ) (r c : Fin (n+1))
    (ha : M.mem a (F.fnSetValue
      (matrixDomain (number (M := M) ((n+1 : ℕ) : ℂ)) (number ((n+1 : ℕ) : ℂ)))
      (M.standard .complex))) :
    matrixComplexOn (F.graphValue (matrixMinorDomain (number (M := M) ((n+1 : ℕ) : ℂ)))
      (M.standard .complex) (matrixMinorBody a (M.number ((n+1 : ℕ) : ℂ))
        (FiniteFunction.index r) (FiniteFunction.index c))) n n =
      (matrixComplexOn a (n+1) (n+1)).submatrix r.succAbove c.succAbove := by
  let order := number (M := M) ((n+1 : ℕ) : ℂ)
  have hr : M.mem (FiniteFunction.index r) (matrixIndexValue order) :=
    matrixIndexNaturalNumber (n+1) (r.val+1) (by omega) (by omega)
  have hc : M.mem (FiniteFunction.index c) (matrixIndexValue order) :=
    matrixIndexNaturalNumber (n+1) (c.val+1) (by omega) (by omega)
  have hp := matrixIndexPositiveOrder order _ hr
  have ret := matrixMinorBody_mem order hp a (FiniteFunction.index r)
    (FiniteFunction.index c) hr hc .complex ha
  ext i j
  have hq : M.mem (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j))
      (matrixMinorDomain order) := by
    rw [matrixMinorDomainSucc]
    exact matrixDomain_pair _ _ _ _
      (matrixIndexNaturalNumber n (i.val+1) (by omega) (by omega))
      (matrixIndexNaturalNumber n (j.val+1) (by omega) (by omega))
  change NativeBridge.complexValue (F.callValue
    (F.graphValue (matrixMinorDomain order) (M.standard .complex)
      (matrixMinorBody a (denote order) (FiniteFunction.index r) (FiniteFunction.index c)))
    (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j))) =
      NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2
        (FiniteFunction.index (r.succAbove i)) (FiniteFunction.index (c.succAbove j))))
  rw [F.call_graphValue _ _ _ ret _ hq]
  unfold matrixMinorBody
  rw [FiniteFunction.unpack_pack2]
  change NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2
    (matrixMinorShift (M.number ((n+1 : ℕ) : ℂ)) (FiniteFunction.index r) (FiniteFunction.index i))
    (matrixMinorShift (M.number ((n+1 : ℕ) : ℂ)) (FiniteFunction.index c) (FiniteFunction.index j)))) = _
  rw [matrixMinorShiftIndex, matrixMinorShiftIndex]

theorem matrixCofactorRawFinSucc {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (n : ℕ) (r c : Fin (n+1))
    (ha : M.mem a (F.fnSetValue
      (matrixDomain (number (M := M) ((n+1 : ℕ) : ℂ)) (number ((n+1 : ℕ) : ℂ)))
      (M.standard .complex))) :
    matrixCofactorRawValue a (M.number ((n+1 : ℕ) : ℂ))
      (FiniteFunction.index r) (FiniteFunction.index c) =
      M.number ((matrixComplexOn a (n+1) (n+1)).adjugate c r) := by
  have hs : M.subValue (M.number ((n+1 : ℕ) : ℂ)) (M.number 1) = M.number (n : ℂ) := by
    rw [M.sub_numbers]
    congr 1
    push_cast
    ring
  have he : NativeBridge.naturalValue (M.addValue (FiniteFunction.index r)
      (FiniteFunction.index c)) = r.val+c.val+2 := by
    unfold FiniteFunction.index
    rw [M.add_numbers]
    have h : (((r.val+1 : ℕ) : ℂ) + ((c.val+1 : ℕ) : ℂ)) =
        ((r.val+c.val+2 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    exact NativeBridge.naturalValue_number _
  change M.number ((-1 : ℂ) ^ NativeBridge.naturalValue
    (M.addValue (FiniteFunction.index r) (FiniteFunction.index c)) *
    (matrixComplexOn (F.graphValue (matrixMinorDomain (number (M := M) ((n+1 : ℕ) : ℂ)))
      (M.standard .complex) (matrixMinorBody a (M.number ((n+1 : ℕ) : ℂ))
        (FiniteFunction.index r) (FiniteFunction.index c)))
      (NativeBridge.naturalValue (M.subValue (M.number ((n+1 : ℕ) : ℂ)) (M.number 1)))
      (NativeBridge.naturalValue (M.subValue (M.number ((n+1 : ℕ) : ℂ)) (M.number 1)))).det) = _
  rw [hs, NativeBridge.naturalValue_number, matrixComplexOnMinorSucc a n r c ha, he,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  congr 1
  rw [pow_add]
  norm_num

theorem matrixComplexValueAdjugate {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    matrixComplexValue (denote (matrixAdjugate a n hn ha)) n n =
      (matrixComplexValue (denote a) n n).adjugate := by
  classical
  unfold matrixComplexValue
  generalize hs : NativeBridge.naturalValue (denote n) = size
  cases size with
  | zero => exact Subsingleton.elim _ _
  | succ k =>
    have hnValue : denote n = M.number ((k+1 : ℕ) : ℂ) := by
      have h := NativeBridge.naturalValue_spec (denote n) hn
      simpa only [hs] using h
    have hd : matrixDomain n n =
        matrixDomain (number (M := M) ((k+1 : ℕ) : ℂ)) (number ((k+1 : ℕ) : ℂ)) := by
      change F.sepValue (FiniteFunction.cartValue ![
        closedRangeValue (M.number 1) (denote n),
        closedRangeValue (M.number 1) (denote n)]) (fun _ => True) = _
      rw [hnValue]
      rfl
    have haNum : M.mem (denote a) (F.fnSetValue
        (matrixDomain (number (M := M) ((k+1 : ℕ) : ℂ)) (number ((k+1 : ℕ) : ℂ)))
        (M.standard .complex)) := by rw [← hd]; exact ha
    ext i j
    have hi : M.mem (FiniteFunction.index i) (matrixIndexValue n) := by
      change M.mem _ (closedRangeValue (M.number 1) (denote n))
      rw [hnValue]
      exact matrixIndexNaturalNumber (k+1) (i.val+1) (by omega) (by omega)
    have hj : M.mem (FiniteFunction.index j) (matrixIndexValue n) := by
      change M.mem _ (closedRangeValue (M.number 1) (denote n))
      rw [hnValue]
      exact matrixIndexNaturalNumber (k+1) (j.val+1) (by omega) (by omega)
    change NativeBridge.complexValue (F.callValue (denote (matrixAdjugate a n hn ha))
      (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j))) =
      (matrixComplexOn (denote a) (k+1) (k+1)).adjugate i j
    rw [matrixAdjugateCall (matrixAdjugate a n hn ha)
      (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j))
      (matrixDomain_pair n n _ _ hi hj)]
    unfold matrixAdjugateBody
    rw [FiniteFunction.unpack_pack2]
    change NativeBridge.complexValue (matrixCofactorRawValue (denote a) (denote n)
      (FiniteFunction.index j) (FiniteFunction.index i)) = _
    rw [hnValue, matrixCofactorRawFinSucc (denote a) k j i haNum,
      NativeBridge.complexValue_number]

theorem matrixMultiplyAdjugateRight {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Same (matrixMultiply a (matrixAdjugate a n hn ha) n n n hn hn hn ha
      (matrixAdjugateInFnSet _))
      (matrixScale (matrixDeterminant a n hn ha) (identityMatrix n hn) n n
        (matrixDeterminantInC _) hn hn (functionRealToComplex (identityMatrixInFnSet _))) := by
  let adj := matrixAdjugate a n hn ha
  let determinant := matrixDeterminant a n hn ha
  let identity := identityMatrix n hn
  let product := matrixMultiply a adj n n n hn hn hn ha (matrixAdjugateInFnSet adj)
  let scaled := matrixScale determinant identity n n (matrixDeterminantInC determinant)
    hn hn (functionRealToComplex (identityMatrixInFnSet identity))
  apply matrixSameOfComplexMatrix product scaled n n hn hn
    (matrixMultiplyInFnSet product) (matrixScaleInFnSet scaled)
  dsimp only [product, scaled, adj, determinant, identity]
  rw [matrixComplexValueMultiply, matrixComplexValueAdjugate, matrixComplexValueScale,
    matrixComplexValue_identity]
  change _ = NativeBridge.complexValue (M.number (matrixComplexValue (denote a) n n).det) • _
  rw [NativeBridge.complexValue_number]
  exact Matrix.mul_adjugate _

theorem matrixMultiplyAdjugateLeft {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Same (matrixMultiply (matrixAdjugate a n hn ha) a n n n hn hn hn
      (matrixAdjugateInFnSet _) ha)
      (matrixScale (matrixDeterminant a n hn ha) (identityMatrix n hn) n n
        (matrixDeterminantInC _) hn hn (functionRealToComplex (identityMatrixInFnSet _))) := by
  let adj := matrixAdjugate a n hn ha
  let determinant := matrixDeterminant a n hn ha
  let identity := identityMatrix n hn
  let product := matrixMultiply adj a n n n hn hn hn (matrixAdjugateInFnSet adj) ha
  let scaled := matrixScale determinant identity n n (matrixDeterminantInC determinant)
    hn hn (functionRealToComplex (identityMatrixInFnSet identity))
  apply matrixSameOfComplexMatrix product scaled n n hn hn
    (matrixMultiplyInFnSet product) (matrixScaleInFnSet scaled)
  dsimp only [product, scaled, adj, determinant, identity]
  rw [matrixComplexValueMultiply, matrixComplexValueAdjugate, matrixComplexValueScale,
    matrixComplexValue_identity]
  change _ = NativeBridge.complexValue (M.number (matrixComplexValue (denote a) n n).det) • _
  rw [NativeBridge.complexValue_number]
  exact Matrix.adjugate_mul _

theorem matrixDeterminantNonzeroComplex {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α)
    (hd : matrixDeterminantValue a n ≠ M.number 0) :
    (matrixComplexValue a n n).det ≠ 0 := by
  intro h
  apply hd
  unfold matrixDeterminantValue
  rw [h]

theorem matrixComplexValueInverse {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hd : matrixDeterminantValue (denote a) n ≠ M.number 0) :
    matrixComplexValue (denote (matrixInverse a n hn ha hd)) n n =
      (matrixComplexValue (denote a) n n).det⁻¹ •
        (matrixComplexValue (denote a) n n).adjugate := by
  let inv := matrixInverse a n hn ha hd
  let adj := matrixAdjugate a n hn ha
  have hdet := matrixDeterminantNonzeroComplex (denote a) n hd
  ext i j
  let q : M.Value := FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j)
  have hq : M.mem q (matrixDomain n n) :=
    matrixDomain_pair n n _ _ (matrixIndexOfFin n hn i) (matrixIndexOfFin n hn j)
  have hmem := F.call_mem _ _ _ _ (matrixAdjugateInFnSet adj) hq
  have hbody : matrixAdjugateBody (denote a) n q =
      M.number (NativeBridge.complexValue (F.callValue (denote adj) q)) :=
    (matrixAdjugateCall adj q hq).symm.trans (NativeBridge.complexValue_spec _ hmem)
  have hentry : NativeBridge.complexValue (F.callValue (denote adj) q) =
      (matrixComplexValue (denote a) n n).adjugate i j :=
    congrFun (congrFun (matrixComplexValueAdjugate a n hn ha) i) j
  have hquot : NativeBridge.complexValue (F.callValue (denote inv) q) =
      NativeBridge.complexValue (F.callValue (denote adj) q) /
        (matrixComplexValue (denote a) n n).det := by
    rw [matrixInverseCall inv q hq]
    change NativeBridge.complexValue (M.divValue (matrixAdjugateBody (denote a) n q)
      (M.number (matrixComplexValue (denote a) n n).det)) = _
    rw [hbody, M.div_numbers _ _ hdet, NativeBridge.complexValue_number]
  change NativeBridge.complexValue (F.callValue (denote inv) q) =
    (matrixComplexValue (denote a) n n).det⁻¹ *
      (matrixComplexValue (denote a) n n).adjugate i j
  exact hquot.trans ((div_eq_mul_inv _ _).trans ((mul_comm _ _).trans
    (congrArg (fun z : ℂ => (matrixComplexValue (denote a) n n).det⁻¹ * z) hentry)))

theorem matrixMultiplyInverseRight {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hd : matrixDeterminantValue (denote a) n ≠ M.number 0) :
    Same (matrixMultiply a (matrixInverse a n hn ha hd) n n n hn hn hn ha
      (matrixInverseInFnSet _)) (identityMatrix n hn) := by
  let inv := matrixInverse a n hn ha hd
  let product := matrixMultiply a inv n n n hn hn hn ha (matrixInverseInFnSet inv)
  apply matrixSameOfComplexMatrix product (identityMatrix n hn) n n hn hn
    (matrixMultiplyInFnSet product) (functionRealToComplex (identityMatrixInFnSet _))
  dsimp only [product, inv]
  have hdet := matrixDeterminantNonzeroComplex (denote a) n hd
  rw [matrixComplexValueMultiply, matrixComplexValueInverse, matrixComplexValue_identity,
    Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hdet, one_smul]

theorem matrixMultiplyInverseLeft {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hd : matrixDeterminantValue (denote a) n ≠ M.number 0) :
    Same (matrixMultiply (matrixInverse a n hn ha hd) a n n n hn hn hn
      (matrixInverseInFnSet _) ha) (identityMatrix n hn) := by
  let inv := matrixInverse a n hn ha hd
  let product := matrixMultiply inv a n n n hn hn hn (matrixInverseInFnSet inv) ha
  apply matrixSameOfComplexMatrix product (identityMatrix n hn) n n hn hn
    (matrixMultiplyInFnSet product) (functionRealToComplex (identityMatrixInFnSet _))
  dsimp only [product, inv]
  have hdet := matrixDeterminantNonzeroComplex (denote a) n hd
  rw [matrixComplexValueMultiply, matrixComplexValueInverse, matrixComplexValue_identity,
    Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ hdet, one_smul]


theorem matrixRankInvertible {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (hd : matrixDeterminantValue (denote a) n ≠ M.number 0) :
    matrixRankValue (denote a) (denote n) (denote n) = denote n := by
  classical
  have hdet := matrixDeterminantNonzeroComplex (denote a) n hd
  have hunit : IsUnit (matrixComplexValue (denote a) n n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  change M.number ((matrixComplexValue (denote a) n n).rank : ℂ) = denote n
  rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  exact (NativeBridge.naturalValue_spec (denote n) hn).symm

end Litex
