import Litex.Analysis

universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem darbouxConstantOneCell (f : M.Value) (a b c : ℝ)
    (equal : ∀ x, M.mem x (riemannClosedIntervalValue (M.number (a : ℂ)) (M.number (b : ℂ))) →
      F.callValue f x=M.number (c : ℂ)) :
    DarbouxApproximationValue f (M.number (a : ℂ)) (M.number (b : ℂ))
      (M.number ((c*(b-a) : ℝ) : ℂ)) := by
  classical
  intro epsilon hepsilon order
  have realA : M.mem (M.number (a : ℂ)) (M.standard .real) := (M.real_members _).mpr ⟨a,rfl⟩
  have realB : M.mem (M.number (b : ℂ)) (M.standard .real) := (M.real_members _).mpr ⟨b,rfl⟩
  have realC : M.mem (M.number (c : ℂ)) (M.standard .real) := (M.real_members _).mpr ⟨c,rfl⟩
  have positiveOne : M.mem (M.number 1) (denote (NPos (M := M))) :=
    numberInNPosOfEq 1 1 (by norm_num) (by decide)
  let pbody : M.Value → M.Value := fun x => if x=M.number 0 then M.number (a : ℂ) else M.number (b : ℂ)
  let partition := F.graphValue (riemannIndexDomain (M.number 0) (M.number 1)) (M.standard .real) pbody
  have pbodyReal (x : M.Value) (_hx : M.mem x (riemannIndexDomain (M.number 0) (M.number 1))) :
      M.mem (pbody x) (M.standard .real) := by
    dsimp only [pbody]
    split_ifs <;> assumption
  have partitionMember : M.mem partition (riemannIndexFnValue (M.number 0) (M.number 1)) :=
    F.graph_inFnSet _ _ _ pbodyReal
  let height := F.graphValue (riemannIndexDomain (M.number 1) (M.number 1)) (M.standard .real) (fun _ => M.number (c : ℂ))
  have heightMember : M.mem height (riemannIndexFnValue (M.number 1) (M.number 1)) :=
    F.graph_inFnSet _ _ _ (fun _ _ => realC)
  have index0 : M.mem (M.number 0) (riemannIndexDomain (M.number 0) (M.number 1)) := by
    simpa only [Int.cast_zero,Int.cast_one] using riemannIndexDomain_number (M := M) 0 1 0 (by omega) (by omega)
  have index1 : M.mem (M.number 1) (riemannIndexDomain (M.number 0) (M.number 1)) := by
    simpa only [Int.cast_zero,Int.cast_one] using riemannIndexDomain_number (M := M) 0 1 1 (by omega) (by omega)
  have heightIndex : M.mem (M.number 1) (riemannIndexDomain (M.number 1) (M.number 1)) := by
    simpa only [Int.cast_one] using riemannIndexDomain_number (M := M) 1 1 1 (by omega) (by omega)
  have p0 : F.callValue partition (M.number 0)=M.number (a : ℂ) := by
    rw [F.call_graphValue _ _ _ pbodyReal _ index0]
    simp only [pbody,ite_true]
  have p1 : F.callValue partition (M.number 1)=M.number (b : ℂ) := by
    rw [F.call_graphValue _ _ _ pbodyReal _ index1]
    have different : M.number (1 : ℂ) ≠ M.number 0 := by
      intro h
      have := M.number_injective h
      norm_num at this
    simp only [pbody,if_neg different]
  have height1 : F.callValue height (M.number 1)=M.number (c : ℂ) :=
    F.call_graphValue _ _ _ (fun _ _ => realC) _ heightIndex
  have oneIndex (k : M.Value) (hk : M.mem k (closedRangeValue (M.number 1) (M.number 1))) : k=M.number 1 := by
    have hk' : M.mem k (closedRangeValue (M.number ((1 : ℤ) : ℂ)) (M.number ((1 : ℤ) : ℂ))) := by simpa only [Int.cast_one] using hk
    obtain ⟨z,hz,lo,hi⟩ := (closedRangeValue_members 1 1 k).mp hk'
    have hz1 : z=1 := by omega
    simpa only [hz1,Int.cast_one] using hz
  have enclosure : DarbouxEnclosureValue f (M.number (a : ℂ)) (M.number (b : ℂ))
      (M.number 1) partition height height := by
    refine ⟨order,positiveOne,partitionMember,heightMember,heightMember,p0,p1,?_,?_⟩
    · intro k hk
      rw [oneIndex k hk,M.sub_numbers,sub_self,p0,p1]
      exact ⟨order,⟨a,a,rfl,rfl,le_rfl⟩,⟨b,b,rfl,rfl,le_rfl⟩⟩
    · intro k hk x hx _ _
      rw [oneIndex k hk,height1,equal x hx]
      exact ⟨⟨c,c,rfl,rfl,le_rfl⟩,⟨c,c,rfl,rfl,le_rfl⟩⟩
  have sumEqual : riemannStepSumValue (M.number 1) partition height=M.number ((c*(b-a) : ℝ) : ℂ) := by
    have h := riemannStepSumValue_nat (M := M) (n := 1) (p := partition) (height := height) (by simpa only [Nat.cast_one] using partitionMember) (by simpa only [Nat.cast_one] using heightMember)
    simpa only [Nat.cast_one,Finset.sum_range_one,Nat.cast_zero,zero_add,height1,p1,p0,observeRealValue_number] using h
  have realSum : M.mem (M.number ((c*(b-a) : ℝ) : ℂ)) (M.standard .real) := (M.real_members _).mpr ⟨c*(b-a),rfl⟩
  let N := semanticObject (M.number 1) (M.member_isSet positiveOne)
  let P := semanticObject partition (M.member_isSet partitionMember)
  let H := semanticObject height (M.member_isSet heightMember)
  let S := semanticObject (M.number ((c*(b-a) : ℝ) : ℂ)) (M.member_isSet realSum)
  refine ⟨N,?_,P,?_,H,?_,H,?_,S,?_,S,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [N,In,semanticObject_denote] using positiveOne
  · simpa only [N,P,semanticObject_denote] using partitionMember
  · simpa only [N,H,semanticObject_denote] using heightMember
  · simpa only [N,H,semanticObject_denote] using heightMember
  · change M.mem _ (M.standard .real)
    exact realSum
  · change M.mem _ (M.standard .real)
    exact realSum
  · simpa only [N,P,H,semanticObject_denote] using enclosure
  · simpa only [N,P,H,S,semanticObject_denote] using sumEqual.symm
  · simpa only [N,P,H,S,semanticObject_denote] using sumEqual.symm
  · simp only [S,semanticObject_denote]
    exact ⟨c*(b-a),c*(b-a),rfl,rfl,le_rfl⟩
  · simp only [S,semanticObject_denote]
    exact ⟨c*(b-a),c*(b-a),rfl,rfl,le_rfl⟩
  · simp only [S,semanticObject_denote,M.sub_numbers,sub_self]
    have he : M.mem epsilon (positiveReal (M := M)) := by simpa only [RPos,semanticObject_denote] using hepsilon
    obtain ⟨e,he,hpos⟩ := ((positiveReal_members epsilon).mp he).2
    exact ⟨0,e,by simp only [Complex.ofReal_zero],he,hpos⟩
theorem riemannIntegralConstantCandidate (f a b c : M.Value)
    (hf : RealFunctionValue M f)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (hc : M.mem c (M.standard .real))
    (cover : ∀ x, M.mem x (riemannIntervalValue a b) → M.mem x (F.domainValue f))
    (equal : ∀ x, M.mem x (riemannIntervalValue a b) → F.callValue f x=c) :
    HasRiemannIntegralValue M f a b (M.mulValue c (M.subValue b a)) := by
  obtain ⟨ar,rfl⟩ := (M.real_members a).mp ha
  obtain ⟨br,rfl⟩ := (M.real_members b).mp hb
  obtain ⟨cr,rfl⟩ := (M.real_members c).mp hc
  have value : M.mulValue (M.number (cr : ℂ))
      (M.subValue (M.number (br : ℂ)) (M.number (ar : ℂ)))=
      M.number ((cr*(br-ar) : ℝ) : ℂ) := by
    rw [M.sub_numbers,M.mul_numbers,Complex.ofReal_mul,Complex.ofReal_sub]
  rw [value]
  have callReal (x : M.Value)
      (hx : M.mem x (riemannIntervalValue (M.number (ar : ℂ)) (M.number (br : ℂ)))) :
      M.mem (F.callValue f x) (M.standard .real) := by
    obtain ⟨signature,member,_,output⟩ := hf
    exact output _ (F.call_mem _ _ _ _ member
      ((F.domainValue_eq signature.domain_isSet member) ▸ cover x hx))
  let D := F.sepValue (riemannIntervalValue (M.number (ar : ℂ)) (M.number (br : ℂ))) (fun _ => True)
  let graph := F.graphValue D (M.standard .real) (F.callValue f)
  have graphMember : M.mem graph (F.fnSetValue D (M.standard .real)) :=
    F.graph_inFnSet _ _ _ (fun x hx => callReal x ((F.sep_members _ _ _).mp hx).1)
  have rangePoint (y : M.Value)
      (hy : M.mem y (riemannRestrictedRangeValue f (M.number (ar : ℂ)) (M.number (br : ℂ)))) :
      y=M.number (cr : ℂ) := by
    change M.mem y (F.rangeValue graph) at hy
    obtain ⟨x,hxy⟩ := ((F.range_spec (isSet (R (M := M))) graphMember).2 y).mp hy
    obtain ⟨hx,_,hvalue⟩ := (F.pair_mem_graph D (M.standard .real) (F.callValue f) x y).mp hxy
    exact hvalue.trans (equal x ((F.sep_members _ _ _).mp hx).1)
  let bound : Obj (M := M) M.Value := semanticObject (M.number (cr : ℂ)) (M.member_isSet hc)
  refine ⟨(M.real_members _).mpr ⟨_,rfl⟩,ha,hb,cover,?_,?_,?_⟩
  · constructor
    · refine ⟨bound,hc,?_⟩
      intro y hy
      exact ⟨cr,cr,rfl,rangePoint y hy,le_rfl⟩
    · refine ⟨bound,hc,?_⟩
      intro y hy
      exact ⟨cr,cr,rangePoint y hy,rfl,le_rfl⟩
  · by_cases h : M.number (ar : ℂ)=M.number (br : ℂ)
    · have ends := Complex.ofReal_injective (M.number_injective h)
      exact Or.inr (by rw [ends,sub_self,mul_zero,Complex.ofReal_zero])
    · exact Or.inl h
  · rw [minMaxValue_number,minMaxValue_number,riemannOrientedValue_number]
    simp only [Bool.false_eq_true,ite_false,ite_true]
    have area : Real.sign (br-ar)*(cr*(br-ar))=cr*(Max.max ar br-Min.min ar br) := by
      rw [max_sub_min_eq_abs,realAbsEqSignMul]
      ring
    rw [area]
    apply darbouxConstantOneCell
    intro x hx
    apply equal x
    unfold riemannIntervalValue
    rw [minMaxValue_number,minMaxValue_number]
    simpa only [Bool.false_eq_true,ite_false,ite_true] using hx
end Litex
