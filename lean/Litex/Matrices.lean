import Litex.Folds

universe u v w x r

namespace Litex

/-- The existing integer interval predicate, expressed directly on denotations. -/
def closedRangeValue {M : Semantics.{u}} [S : SetSemantics M]
    (a b : M.Value) : M.Value :=
  S.sepValue (M.standard .integer) (fun value =>
    ∃ lower upper k : ℤ, a = M.number (lower : ℂ) ∧ b = M.number (upper : ℂ) ∧
      value = M.number (k : ℂ) ∧ lower ≤ k ∧ k ≤ upper)

structure MatrixSetObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  carrier : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ

def matrixIndexValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (dimension : Obj (M := M) α) : M.Value :=
  F.sepValue (M.standard .integer) (ClosedRangeObj.condition ⟨number 1, dimension⟩)

theorem matrixIndexValue_isSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (dimension : Obj (M := M) α) :
    M.isSet (matrixIndexValue dimension) := F.sep_isSet _ _ (M.standard_isSet .integer)

noncomputable def matrixDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) : M.Value :=
  F.sepValue (FiniteFunction.cartValue ![matrixIndexValue rows, matrixIndexValue cols])
    (fun _ => True)

noncomputable def realMatrixDomainValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (rows cols : M.Value) : M.Value :=
  F.sepValue (FiniteFunction.cartValue ![
    closedRangeValue (M.number 1) rows, closedRangeValue (M.number 1) cols]) (fun _ => True)

theorem matrixDomain_isSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) : M.isSet (matrixDomain rows cols) :=
  F.sep_isSet _ _ (FiniteFunction.cart_isSet _ (by
    intro i; fin_cases i <;> exact matrixIndexValue_isSet _))

noncomputable instance matrixSetRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixSetObj (M := M) α β γ) where
  wd s := IsSet s.carrier ∧ In s.rows N ∧ In s.cols N
  denote s := F.fnSetValue (matrixDomain s.rows s.cols) (denote s.carrier)
  wd_isSet {s} h := F.fnSet_isSet _ _ (matrixDomain_isSet s.rows s.cols) h.1

noncomputable def matrixSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (S : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hS : IsSet S) (hm : In m N) (hn : In n N) :
    Obj (M := M) (MatrixSetObj (M := M) α β γ) := ⟨⟨S,m,n⟩,hS,hm,hn⟩

noncomputable def matrixSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (s : Obj (M := M) (MatrixSetObj (M := M) α β γ)) : FunctionSignature M :=
  ⟨matrixDomain s.val.rows s.val.cols, matrixDomain_isSet s.val.rows s.val.cols,
    denote s.val.carrier, s.wd.1⟩

theorem matrixSet_eq_fnSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (s : Obj (M := M) (MatrixSetObj (M := M) α β γ)) :
    Same s (fnSet (matrixSignature s)) := rfl
end Litex

namespace Litex

structure ZeroMatrixObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  rows : Obj (M := M) α
  cols : Obj (M := M) β

noncomputable def zeroMatrixSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) : FunctionSignature M :=
  ⟨matrixDomain m n, matrixDomain_isSet m n, M.standard .real, M.standard_isSet .real⟩

noncomputable instance zeroMatrixRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (ZeroMatrixObj (M := M) α β) where
  wd a := In a.rows N ∧ In a.cols N
  denote a := F.graphValue (matrixDomain a.rows a.cols) (M.standard .real) (fun _ => M.number 0)
  wd_isSet {a} _ := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun _ _ => (M.real_members _).mpr ⟨0, by simp only [Complex.ofReal_zero]⟩))

noncomputable def zeroMatrix {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (hm : In m N) (hn : In n N) :
    Obj (M := M) (ZeroMatrixObj (M := M) α β) := ⟨⟨m,n⟩,hm,hn⟩

theorem zeroMatrixInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (ZeroMatrixObj (M := M) α β)) :
    In p (fnSet (zeroMatrixSignature p.val.rows p.val.cols)) :=
  FunctionSemantics.graph_inFnSet _ _ _
    (fun _ _ => (M.real_members _).mpr ⟨0, by simp only [Complex.ofReal_zero]⟩)

theorem zeroMatrixCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (ZeroMatrixObj (M := M) α β)) (x : M.Value)
    (hx : M.mem x (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) x = M.number 0 :=
  F.call_graphValue _ _ _
    (fun _ _ => (M.real_members _).mpr ⟨0, by simp only [Complex.ofReal_zero]⟩) x hx

theorem functionRealToComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {D f : M.Value} (h : M.mem f (F.fnSetValue D (M.standard .real))) :
    M.mem f (F.fnSetValue D (M.standard .complex)) :=
  F.fnSet_of_returns h (fun x hx => M.real_subset_complex _ (F.call_mem _ _ _ x h hx))
end Litex

namespace Litex

theorem matrixDomain_swap {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) (p : M.Value)
    (hp : M.mem p (matrixDomain rows cols)) :
    M.mem (FiniteFunction.pack2 (FiniteFunction.unpack2 p).2 (FiniteFunction.unpack2 p).1)
      (matrixDomain cols rows) := by
  have base := ((F.sep_members _ _ _).mp hp).1
  obtain ⟨a, ha, b, hb, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp base
  apply (F.sep_members _ _ _).mpr
  refine ⟨?_, True.intro⟩
  rw [FiniteFunction.unpack_pack2]
  exact (FiniteFunction.cart2_members _ _ _).mpr ⟨b,hb,a,ha,rfl⟩

structure MatrixTransposeObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ

noncomputable def matrixTransposeBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (a p : M.Value) : M.Value :=
  F.callValue a (FiniteFunction.pack2 (FiniteFunction.unpack2 p).2 (FiniteFunction.unpack2 p).1)

noncomputable def matrixTransposeSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) (S : StandardSetValue) : FunctionSignature M :=
  ⟨matrixDomain cols rows, matrixDomain_isSet cols rows, M.standard S, M.standard_isSet S⟩

noncomputable instance matrixTransposeRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixTransposeObj (M := M) α β γ) where
  wd a := In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.matrix) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.cols a.rows) (M.standard .complex)
    (matrixTransposeBody (denote a.matrix))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun p hp => F.call_mem _ _ _ _ h.2.2 (matrixDomain_swap a.cols a.rows p hp)))

noncomputable def transpose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixTransposeObj (M := M) α β γ) := ⟨⟨A,m,n⟩,hm,hn,hA⟩

theorem transposeInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ)) :
    In p (fnSet (matrixTransposeSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => F.call_mem _ _ _ _ p.wd.2.2 (matrixDomain_swap p.val.cols p.val.rows q hq))

theorem transposeCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.cols p.val.rows)) :
    F.callValue (denote p) q = matrixTransposeBody (denote p.val.matrix) q :=
  F.call_graphValue _ _ _
    (fun x hx => F.call_mem _ _ _ _ p.wd.2.2 (matrixDomain_swap p.val.cols p.val.rows x hx)) q hq

theorem transposeInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ))
    (hA : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixTransposeSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (transposeInFnSet p)
  intro q hq
  rw [transposeCall p q hq]
  exact F.call_mem _ _ _ _ hA (matrixDomain_swap p.val.cols p.val.rows q hq)
end Litex

namespace Litex

theorem transpose_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.cols p.val.rows)
    (hbody : g.val.bodyValue = matrixTransposeBody (denote p.val.matrix)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixTransposeSignature p.val.rows p.val.cols .complex) g.val.signature
    (transposeInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [transposeCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex

theorem conjugateValueInComplex {M : Semantics.{u}} (a : M.Value)
    (h : M.mem a (M.standard .complex)) :
    M.mem (complexUnaryValue (fun z : ℂ => star z) a) (M.standard .complex) := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp h
  rw [hz, complexUnaryValue_number]
  exact (M.complex_members _).mpr ⟨star z,rfl⟩

theorem conjugateValueInReal {M : Semantics.{u}} (a : M.Value)
    (h : M.mem a (M.standard .real)) :
    M.mem (complexUnaryValue (fun z : ℂ => star z) a) (M.standard .real) := by
  obtain ⟨z,hz⟩ := (M.real_members _).mp h
  rw [hz, complexUnaryValue_number]
  exact (M.real_members _).mpr ⟨z,congrArg M.number (Complex.conj_ofReal z)⟩

structure MatrixConjugateTransposeObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ

noncomputable def matrixConjugateTransposeBody {M : Semantics.{u}} [FunctionSemantics M]
    (a p : M.Value) : M.Value :=
  complexUnaryValue (fun z : ℂ => star z) (matrixTransposeBody a p)

noncomputable instance matrixConjugateTransposeRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixConjugateTransposeObj (M := M) α β γ) where
  wd a := In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.matrix) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.cols a.rows) (M.standard .complex)
    (matrixConjugateTransposeBody (denote a.matrix))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun p hp => conjugateValueInComplex _
      (F.call_mem _ _ _ _ h.2.2 (matrixDomain_swap a.cols a.rows p hp))))

noncomputable def conjugateTranspose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ) := ⟨⟨A,m,n⟩,hm,hn,hA⟩

theorem conjugateTransposeInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ)) :
    In p (fnSet (matrixTransposeSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => conjugateValueInComplex _
      (F.call_mem _ _ _ _ p.wd.2.2 (matrixDomain_swap p.val.cols p.val.rows q hq)))

theorem conjugateTransposeCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.cols p.val.rows)) :
    F.callValue (denote p) q = matrixConjugateTransposeBody (denote p.val.matrix) q :=
  F.call_graphValue _ _ _
    (fun x hx => conjugateValueInComplex _
      (F.call_mem _ _ _ _ p.wd.2.2 (matrixDomain_swap p.val.cols p.val.rows x hx))) q hq

theorem conjugateTransposeInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ))
    (hA : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixTransposeSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (conjugateTransposeInFnSet p)
  intro q hq
  rw [conjugateTransposeCall p q hq]
  exact conjugateValueInReal _
    (F.call_mem _ _ _ _ hA (matrixDomain_swap p.val.cols p.val.rows q hq))

theorem conjugateTranspose_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.cols p.val.rows)
    (hbody : g.val.bodyValue = matrixConjugateTransposeBody (denote p.val.matrix)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixTransposeSignature p.val.rows p.val.cols .complex) g.val.signature
    (conjugateTransposeInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [conjugateTransposeCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex

/-- The source identity formula is the size of the intersection of two singletons. -/
noncomputable def matrixIdentityEntry {M : Semantics.{u}} [S : SetSemantics M]
    (row col : M.Value) : M.Value :=
  M.number (finiteCard (S.sepValue (S.insertValue row S.emptyValue)
    (fun x => M.mem x (S.insertValue col S.emptyValue))) : ℂ)

theorem matrixIdentityEntry_inReal {M : Semantics.{u}} [S : SetSemantics M]
    (row col : M.Value) : M.mem (matrixIdentityEntry row col) (M.standard .real) := by
  exact (M.real_members _).mpr ⟨_, rfl⟩

noncomputable def matrixIdentityBody {M : Semantics.{u}} [FunctionSemantics M]
    (p : M.Value) : M.Value :=
  matrixIdentityEntry (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2

structure IdentityMatrixObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  order : Obj (M := M) α

noncomputable def identityMatrixSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) : FunctionSignature M :=
  ⟨matrixDomain n n, matrixDomain_isSet n n, M.standard .real, M.standard_isSet .real⟩

noncomputable instance identityMatrixRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] : Representation M (IdentityMatrixObj (M := M) α) where
  wd a := In a.order N
  denote a := F.graphValue (matrixDomain a.order a.order) (M.standard .real) matrixIdentityBody
  wd_isSet _ := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun _ _ => matrixIdentityEntry_inReal _ _))

noncomputable def identityMatrix {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N) :
    Obj (M := M) (IdentityMatrixObj (M := M) α) := ⟨⟨n⟩,hn⟩

theorem identityMatrixInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) (IdentityMatrixObj (M := M) α)) :
    In p (fnSet (identityMatrixSignature p.val.order)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _)

theorem identityMatrixCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (IdentityMatrixObj (M := M) α)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.order p.val.order)) :
    F.callValue (denote p) q = matrixIdentityBody q :=
  F.call_graphValue _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _) q hq

end Litex

namespace Litex

theorem finiteSetIntersect {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (IntersectObj (M := M) α β))
    (hA : IsFiniteSet p.val.left) (_hB : IsFiniteSet p.val.right) : IsFiniteSet p := by
  apply hA.subset
  intro x hx
  exact ((S.sep_members _ _ _).mp hx).1

theorem finiteSetIntersectFromLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (IntersectObj (M := M) α β))
    (hA : IsFiniteSet p.val.left) : IsFiniteSet p := by
  apply hA.subset
  intro x hx
  exact ((S.sep_members _ _ _).mp hx).1

theorem finiteSetIntersectFromRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (IntersectObj (M := M) α β))
    (hB : IsFiniteSet p.val.right) : IsFiniteSet p := by
  apply hB.subset
  intro x hx
  exact ((S.sep_members _ _ _).mp hx).2
end Litex

namespace Litex
theorem matrixIdentityEntrySelf {M : Semantics.{u}} [S : SetSemantics M]
    (a : M.Value) : matrixIdentityEntry a a = M.number 1 := by
  have h : memberSet (S.sepValue (S.insertValue a S.emptyValue)
      (fun x => M.mem x (S.insertValue a S.emptyValue))) = {a} := by
    ext x
    simp only [memberSet, Set.mem_setOf_eq, S.sep_members, S.insert_members,
      S.empty_members, or_false, and_self, Set.mem_singleton_iff]
  unfold matrixIdentityEntry finiteCard
  rw [h, Set.ncard_singleton]
  norm_num

theorem matrixIdentityEntryDifferent {M : Semantics.{u}} [S : SetSemantics M]
    (a b : M.Value) (hab : a ≠ b) : matrixIdentityEntry a b = M.number 0 := by
  have h : memberSet (S.sepValue (S.insertValue a S.emptyValue)
      (fun x => M.mem x (S.insertValue b S.emptyValue))) = ∅ := by
    ext x
    simp only [memberSet, Set.mem_setOf_eq, S.sep_members, S.insert_members,
      S.empty_members, or_false, Set.mem_empty_iff_false, iff_false, not_and]
    intro hxa hxb
    exact hab (hxa.symm.trans hxb)
  unfold matrixIdentityEntry finiteCard
  rw [h, Set.ncard_empty]
  norm_num
end Litex

namespace Litex
inductive MatrixEntrywiseOp where
  | add
  | sub

def matrixEntrywiseValue {M : Semantics.{u}} (op : MatrixEntrywiseOp) (a b : M.Value) : M.Value :=
  match op with
  | .add => M.addValue a b
  | .sub => M.subValue a b

theorem matrixEntrywiseValue_complex {M : Semantics.{u}} (op : MatrixEntrywiseOp)
    {a b : M.Value} (ha : M.mem a (M.standard .complex)) (hb : M.mem b (M.standard .complex)) :
    M.mem (matrixEntrywiseValue op a b) (M.standard .complex) := by
  cases op with
  | add => exact M.add_closed ha hb
  | sub => exact Semantics.sub_closed ha hb

theorem matrixEntrywiseValue_real {M : Semantics.{u}} (op : MatrixEntrywiseOp)
    {a b : M.Value} (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real)) :
    M.mem (matrixEntrywiseValue op a b) (M.standard .real) := by
  obtain ⟨a, rfl⟩ := (M.real_members _).mp ha
  obtain ⟨b, rfl⟩ := (M.real_members _).mp hb
  cases op with
  | add => exact (M.real_members _).mpr ⟨a+b, by
      change M.addValue _ _ = _
      rw [M.add_numbers, Complex.ofReal_add]⟩
  | sub => exact (M.real_members _).mpr ⟨a-b, by
      change M.subValue _ _ = _
      rw [M.sub_numbers, Complex.ofReal_sub]⟩

structure MatrixEntrywiseObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  operation : MatrixEntrywiseOp
  left : Obj (M := M) α
  right : Obj (M := M) β
  rows : Obj (M := M) γ
  cols : Obj (M := M) δ

theorem matrixDomain_repack {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (p : M.Value)
    (hp : M.mem p (matrixDomain m n)) :
    M.mem (FiniteFunction.pack2 (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2)
      (matrixDomain m n) := by
  have base := ((F.sep_members _ _ _).mp hp).1
  obtain ⟨a, _, b, _, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp base
  simpa only [FiniteFunction.unpack_pack2] using hp

noncomputable def matrixEntrywiseBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (op : MatrixEntrywiseOp) (a b p : M.Value) : M.Value :=
  matrixEntrywiseValue op
    (F.callValue a (FiniteFunction.pack2 (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2))
    (F.callValue b (FiniteFunction.pack2 (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2))

noncomputable def matrixEntrywiseSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) (S : StandardSetValue) : FunctionSignature M :=
  ⟨matrixDomain rows cols, matrixDomain_isSet rows cols, M.standard S, M.standard_isSet S⟩

noncomputable instance matrixEntrywiseRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixEntrywiseObj (M := M) α β γ δ) where
  wd a := In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.left) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex)) ∧
    M.mem (denote a.right) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.rows a.cols) (M.standard .complex)
    (matrixEntrywiseBody a.operation (denote a.left) (denote a.right))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => matrixEntrywiseValue_complex a.operation
      (F.call_mem _ _ _ _ h.2.2.1 (matrixDomain_repack a.rows a.cols q hq)) (F.call_mem _ _ _ _ h.2.2.2 (matrixDomain_repack a.rows a.cols q hq))))

noncomputable def matrixEntrywise {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (op : MatrixEntrywiseOp) (A : Obj (M := M) α) (B : Obj (M := M) β)
    (m : Obj (M := M) γ) (n : Obj (M := M) δ) (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hB : M.mem (denote B) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ) := ⟨⟨op,A,B,m,n⟩,hm,hn,hA,hB⟩

theorem matrixEntrywiseInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ)) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun q hq => matrixEntrywiseValue_complex p.val.operation
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_repack p.val.rows p.val.cols q hq)) (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_repack p.val.rows p.val.cols q hq)))

theorem matrixEntrywiseCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) q = matrixEntrywiseBody p.val.operation (denote p.val.left) (denote p.val.right) q :=
  F.call_graphValue _ _ _ (fun x hx => matrixEntrywiseValue_complex p.val.operation
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_repack p.val.rows p.val.cols x hx)) (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_repack p.val.rows p.val.cols x hx))) q hq

theorem matrixEntrywiseInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ))
    (hA : M.mem (denote p.val.left) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real)))
    (hB : M.mem (denote p.val.right) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (matrixEntrywiseInFnSet p)
  intro q hq
  rw [matrixEntrywiseCall p q hq]
  exact matrixEntrywiseValue_real _ (F.call_mem _ _ _ _ hA (matrixDomain_repack p.val.rows p.val.cols q hq)) (F.call_mem _ _ _ _ hB (matrixDomain_repack p.val.rows p.val.cols q hq))

theorem matrixEntrywise_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.rows p.val.cols)
    (hbody : g.val.bodyValue = matrixEntrywiseBody p.val.operation (denote p.val.left) (denote p.val.right)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.rows p.val.cols .complex) g.val.signature
    (matrixEntrywiseInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixEntrywiseCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
structure MatrixScaleObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  scalar : Obj (M := M) α
  matrix : Obj (M := M) β
  rows : Obj (M := M) γ
  cols : Obj (M := M) δ

noncomputable def matrixScaleBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (z a p : M.Value) : M.Value :=
  M.mulValue z (F.callValue a
    (FiniteFunction.pack2 (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2))

noncomputable instance matrixScaleRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixScaleObj (M := M) α β γ δ) where
  wd a := In a.scalar C ∧ In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.matrix) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.rows a.cols) (M.standard .complex)
    (matrixScaleBody (denote a.scalar) (denote a.matrix))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => Semantics.mul_closed h.1
      (F.call_mem _ _ _ _ h.2.2.2 (matrixDomain_repack a.rows a.cols q hq))))

noncomputable def matrixScale {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (z : Obj (M := M) α) (A : Obj (M := M) β) (m : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hz : In z C) (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixScaleObj (M := M) α β γ δ) := ⟨⟨z,A,m,n⟩,hz,hm,hn,hA⟩

theorem matrixScaleInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ)) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun q hq => Semantics.mul_closed p.wd.1
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_repack p.val.rows p.val.cols q hq)))

theorem matrixScaleCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) q = matrixScaleBody (denote p.val.scalar) (denote p.val.matrix) q :=
  F.call_graphValue _ _ _ (fun x hx => Semantics.mul_closed p.wd.1
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_repack p.val.rows p.val.cols x hx))) q hq

theorem matrixScaleInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ))
    (hA : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real)))
    (hz : In p.val.scalar R) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (matrixScaleInFnSet p)
  intro q hq
  rw [matrixScaleCall p q hq]
  obtain ⟨z,hz⟩ := (M.real_members _).mp hz
  obtain ⟨a,ha⟩ := (M.real_members _).mp
    (F.call_mem _ _ _ _ hA (matrixDomain_repack p.val.rows p.val.cols q hq))
  exact (M.real_members _).mpr ⟨z*a, by
    change M.mulValue _ _ = _
    rw [hz, ha, M.mul_numbers, Complex.ofReal_mul]⟩

theorem matrixScale_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.rows p.val.cols)
    (hbody : g.val.bodyValue = matrixScaleBody (denote p.val.scalar) (denote p.val.matrix)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.rows p.val.cols .complex) g.val.signature
    (matrixScaleInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixScaleCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
theorem matrixDomain_first {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (p : M.Value)
    (hp : M.mem p (matrixDomain m n)) :
    M.mem (FiniteFunction.unpack2 p).1 (finiteSeqDomain m) := by
  have base := ((F.sep_members _ _ _).mp hp).1
  obtain ⟨a, ha, b, _, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp base
  rw [FiniteFunction.unpack_pack2]
  exact (F.sep_members _ _ _).mpr ⟨ha, True.intro⟩

theorem matrixDomain_second {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (p : M.Value)
    (hp : M.mem p (matrixDomain m n)) :
    M.mem (FiniteFunction.unpack2 p).2 (finiteSeqDomain n) := by
  have base := ((F.sep_members _ _ _).mp hp).1
  obtain ⟨a, _, b, hb, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp base
  rw [FiniteFunction.unpack_pack2]
  exact (F.sep_members _ _ _).mpr ⟨hb, True.intro⟩

theorem mulValuesInReal {M : Semantics.{u}} {a b : M.Value}
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real)) :
    M.mem (M.mulValue a b) (M.standard .real) := by
  obtain ⟨a,rfl⟩ := (M.real_members _).mp ha
  obtain ⟨b,rfl⟩ := (M.real_members _).mp hb
  exact (M.real_members _).mpr ⟨a*b, by rw [M.mul_numbers, Complex.ofReal_mul]⟩

structure MatrixOuterObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  left : Obj (M := M) α
  right : Obj (M := M) β
  rows : Obj (M := M) γ
  cols : Obj (M := M) δ

noncomputable def matrixOuterBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b p : M.Value) : M.Value :=
  M.mulValue (F.callValue a (FiniteFunction.unpack2 p).1)
    (F.callValue b (FiniteFunction.unpack2 p).2)

noncomputable instance matrixOuterRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixOuterObj (M := M) α β γ δ) where
  wd a := In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.left) (F.fnSetValue (finiteSeqDomain a.rows) (M.standard .complex)) ∧
    M.mem (denote a.right) (F.fnSetValue (finiteSeqDomain a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.rows a.cols) (M.standard .complex)
    (matrixOuterBody (denote a.left) (denote a.right))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => Semantics.mul_closed
      (F.call_mem _ _ _ _ h.2.2.1 (matrixDomain_first a.rows a.cols q hq))
      (F.call_mem _ _ _ _ h.2.2.2 (matrixDomain_second a.rows a.cols q hq))))

noncomputable def matrixOuter {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (m : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (finiteSeqDomain m) (M.standard .complex)))
    (hB : M.mem (denote B) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (MatrixOuterObj (M := M) α β γ δ) := ⟨⟨A,B,m,n⟩,hm,hn,hA,hB⟩

theorem matrixOuterInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixOuterObj (M := M) α β γ δ)) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun q hq => Semantics.mul_closed
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_first p.val.rows p.val.cols q hq))
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_second p.val.rows p.val.cols q hq)))

theorem matrixOuterCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixOuterObj (M := M) α β γ δ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) q = matrixOuterBody (denote p.val.left) (denote p.val.right) q :=
  F.call_graphValue _ _ _ (fun x hx => Semantics.mul_closed
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_first p.val.rows p.val.cols x hx))
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_second p.val.rows p.val.cols x hx))) q hq

theorem matrixOuterInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixOuterObj (M := M) α β γ δ))
    (hA : M.mem (denote p.val.left) (F.fnSetValue (finiteSeqDomain p.val.rows) (M.standard .real)))
    (hB : M.mem (denote p.val.right) (F.fnSetValue (finiteSeqDomain p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (matrixOuterInFnSet p)
  intro q hq
  rw [matrixOuterCall p q hq]
  exact mulValuesInReal
    (F.call_mem _ _ _ _ hA (matrixDomain_first p.val.rows p.val.cols q hq))
    (F.call_mem _ _ _ _ hB (matrixDomain_second p.val.rows p.val.cols q hq))

theorem matrixOuter_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixOuterObj (M := M) α β γ δ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.rows p.val.cols)
    (hbody : g.val.bodyValue = matrixOuterBody (denote p.val.left) (denote p.val.right)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.rows p.val.cols .complex) g.val.signature
    (matrixOuterInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixOuterCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
theorem tupleInFunctionSet {M : Semantics.{u}} [F : FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) (s : FunctionSignature M)
    (hd : s.domain = FiniteFunction.indexSet n)
    (hc : ∀ i, M.mem (t.val.values i) s.output) : In t (fnSet s) := by
  have graph : M.mem (denote t) (F.fnSetValue (FiniteFunction.indexSet n)
      (FiniteFunction.finiteSetValue (List.ofFn t.val.values))) :=
    (F.fnSet_members _ _ _).mpr (FiniteFunction.tuple_isFunction t.val.values)
  rw [← hd] at graph
  apply F.fnSet_of_returns graph
  intro x hx
  rw [hd] at hx
  obtain ⟨i,rfl⟩ := (FiniteFunction.indexSet_members x).mp hx
  rw [tuple_coordinate]
  exact hc i
end Litex

namespace Litex
structure MatrixDiagonalObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  vector : Obj (M := M) α
  order : Obj (M := M) β

noncomputable def matrixDiagonalBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (a p : M.Value) : M.Value :=
  M.mulValue (matrixIdentityEntry (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2)
    (F.callValue a (FiniteFunction.unpack2 p).1)

theorem matrixDiagonalBody_closed {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β)
    (ha : M.mem a (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (p : M.Value) (hp : M.mem p (matrixDomain n n)) :
    M.mem (matrixDiagonalBody a p) (M.standard .complex) :=
  Semantics.mul_closed (M.real_subset_complex _ (matrixIdentityEntry_inReal _ _))
    (F.call_mem _ _ _ _ ha (matrixDomain_first n n p hp))

noncomputable instance matrixDiagonalRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixDiagonalObj (M := M) α β) where
  wd a := In a.order N ∧
    M.mem (denote a.vector) (F.fnSetValue (finiteSeqDomain a.order) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.order a.order) (M.standard .complex)
    (matrixDiagonalBody (denote a.vector))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (matrixDiagonalBody_closed _ a.order h.2))

noncomputable def matrixDiagonal {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (v : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (hv : M.mem (denote v) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (MatrixDiagonalObj (M := M) α β) := ⟨⟨v,n⟩,hn,hv⟩

theorem matrixDiagonalInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDiagonalObj (M := M) α β)) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (matrixDiagonalBody_closed _ p.val.order p.wd.2)

theorem matrixDiagonalCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDiagonalObj (M := M) α β)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.order p.val.order)) :
    F.callValue (denote p) q = matrixDiagonalBody (denote p.val.vector) q :=
  F.call_graphValue _ _ _ (matrixDiagonalBody_closed _ p.val.order p.wd.2) q hq

theorem matrixDiagonalInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDiagonalObj (M := M) α β))
    (hv : M.mem (denote p.val.vector) (F.fnSetValue (finiteSeqDomain p.val.order) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .real)) := by
  apply F.fnSet_of_returns (matrixDiagonalInFnSet p)
  intro q hq
  rw [matrixDiagonalCall p q hq]
  exact mulValuesInReal (matrixIdentityEntry_inReal _ _)
    (F.call_mem _ _ _ _ hv (matrixDomain_first p.val.order p.val.order q hq))

theorem matrixDiagonal_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDiagonalObj (M := M) α β)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.order p.val.order)
    (hbody : g.val.bodyValue = matrixDiagonalBody (denote p.val.vector)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.order p.val.order .complex) g.val.signature
    (matrixDiagonalInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixDiagonalCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
/-- Finite numerical aggregation over an explicitly represented input set. -/
structure FiniteAggregateOnObj {M : Semantics.{u}} (product : Bool)
    (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  set : Obj (M := M) α
  function : Obj (M := M) β
  input : Obj (M := M) γ
  signature : FunctionSignature M

noncomputable instance finiteAggregateOnRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] (product : Bool)
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (FiniteAggregateOnObj (M := M) product α β γ) where
  wd p := IsFiniteSet p.set ∧ Subset p.set p.input ∧
    (∀ y, M.mem y p.signature.output → M.mem y (M.standard .complex)) ∧
    In p.function (fnSet p.signature) ∧
    (∀ x, M.mem x (denote p.input) → M.mem x p.signature.domain)
  denote p := M.number (finiteAggregateValue product (denote p.set)
    (fun x => NativeBridge.complexValue (F.callValue (denote p.function) x)))
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def finiteAggregateOn {M : Semantics.{u}} [FunctionSemantics M]
    (product : Bool) {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (f : Obj (M := M) β) (input : Obj (M := M) γ)
    (s : FunctionSignature M) (hf : IsFiniteSet A) (hi : Subset A input)
    (hr : ∀ y, M.mem y s.output → M.mem y (M.standard .complex))
    (hfn : In f (fnSet s))
    (hd : ∀ x, M.mem x (denote input) → M.mem x s.domain) :
    Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ) :=
  ⟨⟨A,f,input,s⟩,hf,hi,hr,hfn,hd⟩

theorem finiteAggregateOnCallInOutput {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ))
    (x : M.Value) (hx : M.mem x (denote p.val.set)) :
    M.mem (F.callValue (denote p.val.function) x) p.val.signature.output :=
  F.call_mem _ _ _ _ p.wd.2.2.2.1 (p.wd.2.2.2.2 x (p.wd.2.1 x hx))

theorem finiteAggregateOnMemberOfOutputSubset {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ))
    (A : StandardSetValue) (hs : ∀ y, M.mem y p.val.signature.output → M.mem y (M.standard A)) :
    In p (standardSet A) := by
  classical
  have hm : ∀ x ∈ p.wd.1.toFinset,
      M.mem (M.number (NativeBridge.complexValue (F.callValue (denote p.val.function) x)))
        (M.standard A) := by
    intro x hx
    have ho := finiteAggregateOnCallInOutput p x (p.wd.1.mem_toFinset.mp hx)
    rw [← NativeBridge.complexValue_spec _ (p.wd.2.2.1 _ ho)]
    exact hs _ ho
  change M.mem (M.number (finiteAggregateValue product _ _)) (M.standard A)
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf]
  generalize p.wd.1.toFinset = s at *
  cases product
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using standardZeroMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact standardAddMember A _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))
  · simp only [↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using standardOneMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact standardMulMember A _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))



theorem finiteAggregateOnMember {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ))
    (A : StandardSetValue) (hs : p.val.signature.output = M.standard A) :
    In p (standardSet A) := by
  apply finiteAggregateOnMemberOfOutputSubset p A
  intro y hy
  rw [← hs]
  exact hy

theorem finiteAggregateOnListDenote {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ))
    (xs : List ℂ) (value : ℂ)
    (hm : ∀ x, M.mem x (denote p.val.set) ↔ x ∈ xs.map M.number)
    (hc : (if product then ∏ x ∈ xs.toFinset,
        NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number x))
      else ∑ x ∈ xs.toFinset,
        NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number x))) = value) :
    denote p = M.number value := by
  classical
  have ht : p.wd.1.toFinset = xs.toFinset.image M.number := by
    ext x
    rw [Set.Finite.mem_toFinset]
    change M.mem x (denote p.val.set) ↔ _
    rw [hm]
    simp only [List.mem_map, Finset.mem_image, List.mem_toFinset]
  change M.number (finiteAggregateValue product _ _) = _
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf, ht]
  apply congrArg M.number
  have hi : ∀ a ∈ xs.toFinset, ∀ b ∈ xs.toFinset, M.number a = M.number b → a = b :=
    fun _ _ _ _ h => M.number_injective h
  cases product
  · simpa only [Bool.false_eq_true, ↓reduceIte, Finset.sum_image hi] using hc
  · simpa only [↓reduceIte, Finset.prod_image hi] using hc

end Litex

namespace Litex
theorem closedRangeFinite {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (ClosedRangeObj (M := M) α β)) : IsFiniteSet p := by
  obtain ⟨a,ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b,hb⟩ := (M.integer_members _).mp p.wd.2
  apply ((Set.finite_Icc a b).image (fun k : ℤ => M.number (k : ℂ))).subset
  intro x hx
  obtain ⟨l,r,k,hl,hr,hx,hlo,hhi⟩ := ((S.sep_members _ _ _).mp hx).2
  have left : l = a := by exact_mod_cast M.number_injective (hl.symm.trans ha)
  have right : r = b := by exact_mod_cast M.number_injective (hr.symm.trans hb)
  subst l; subst r
  exact ⟨k, ⟨hlo,hhi⟩, hx.symm⟩

theorem rangeFinite {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (RangeObj (M := M) α β)) : IsFiniteSet p := by
  obtain ⟨a,ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b,hb⟩ := (M.integer_members _).mp p.wd.2
  apply ((Set.finite_Icc a b).image (fun k : ℤ => M.number (k : ℂ))).subset
  intro x hx
  obtain ⟨l,r,k,hl,hr,hx,hlo,hhi⟩ := ((S.sep_members _ _ _).mp hx).2
  have left : l = a := by exact_mod_cast M.number_injective (hl.symm.trans ha)
  have right : r = b := by exact_mod_cast M.number_injective (hr.symm.trans hb)
  subst l; subst r
  exact ⟨k, ⟨hlo,hhi.le⟩, hx.symm⟩
end Litex

namespace Litex

theorem finiteAggregateValueMember {M : Semantics.{u}} (product : Bool)
    (A : M.Value) (value : M.Value → ℂ) (S : StandardSetValue)
    (hf : (memberSet A).Finite)
    (hv : ∀ x, M.mem x A → M.mem (M.number (value x)) (M.standard S)) :
    M.mem (M.number (finiteAggregateValue product A value)) (M.standard S) := by
  classical
  unfold finiteAggregateValue
  rw [dif_pos hf]
  have hm : ∀ x ∈ hf.toFinset, M.mem (M.number (value x)) (M.standard S) :=
    fun x hx => hv x (hf.mem_toFinset.mp hx)
  generalize hf.toFinset = s at *
  cases product
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using standardZeroMember (M := M) S
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact standardAddMember S _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))
  · simp only [↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using standardOneMember (M := M) S
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact standardMulMember S _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))

theorem finiteAggregateValue_congr {M : Semantics.{u}} (product : Bool)
    (A : M.Value) (f g : M.Value → ℂ) (h : ∀ x, M.mem x A → f x = g x) :
    finiteAggregateValue product A f = finiteAggregateValue product A g := by
  classical
  unfold finiteAggregateValue
  by_cases hf : (memberSet A).Finite
  · simp only [dif_pos hf]
    cases product
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact Finset.sum_congr rfl (fun x hx => h x (hf.mem_toFinset.mp hx))
    · simp only [↓reduceIte]
      exact Finset.prod_congr rfl (fun x hx => h x (hf.mem_toFinset.mp hx))
  · simp only [dif_neg hf]

theorem matrixIndexFinite {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N) :
    (memberSet (matrixIndexValue n)).Finite :=
  closedRangeFinite (closedRange (number 1) n
    (NativeBridge.numberInZOfEq 1 1 (by norm_num)) (naturalToInteger n hn))

theorem finiteAggregateValueList {M : Semantics.{u}} (product : Bool)
    (A : M.Value) (f : M.Value → ℂ) (xs : List ℂ) (value : ℂ)
    (hm : ∀ x, M.mem x A ↔ x ∈ xs.map M.number)
    (hc : (if product then ∏ x ∈ xs.toFinset, f (M.number x)
      else ∑ x ∈ xs.toFinset, f (M.number x)) = value) :
    finiteAggregateValue product A f = value := by
  classical
  have hs : memberSet A = (xs.toFinset.image M.number : Set M.Value) := by
    ext x
    change M.mem x A ↔ _
    rw [hm]
    simp only [Finset.mem_coe, List.mem_map, Finset.mem_image, List.mem_toFinset]
  have hf : (memberSet A).Finite := hs ▸ (xs.toFinset.image M.number).finite_toSet
  have ht : hf.toFinset = xs.toFinset.image M.number := by
    ext x
    rw [Set.Finite.mem_toFinset, hs]
    rfl
  unfold finiteAggregateValue
  rw [dif_pos hf, ht]
  have hi : ∀ a ∈ xs.toFinset, ∀ b ∈ xs.toFinset, M.number a = M.number b → a = b :=
    fun _ _ _ _ h => M.number_injective h
  cases product
  · simpa only [Bool.false_eq_true, ↓reduceIte, Finset.sum_image hi] using hc
  · simpa only [↓reduceIte, Finset.prod_image hi] using hc

theorem finiteAggregateValueEmpty {M : Semantics.{u}} (product : Bool)
    (A : M.Value) (f : M.Value → ℂ) (h : ∀ x, ¬ M.mem x A) :
    finiteAggregateValue product A f = if product then 1 else 0 := by
  classical
  have hs : memberSet A = ∅ := by
    ext x
    exact ⟨fun hx => False.elim (h x hx), fun hx => False.elim hx⟩
  have hf : (memberSet A).Finite := by rw [hs]; exact Set.finite_empty
  have ht : hf.toFinset = ∅ := by
    ext x
    simp [memberSet, h]
  unfold finiteAggregateValue
  rw [dif_pos hf, ht]
  cases product <;> simp

theorem matrixDomain_pair {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (a b : M.Value)
    (ha : M.mem a (matrixIndexValue m)) (hb : M.mem b (matrixIndexValue n)) :
    M.mem (FiniteFunction.pack2 a b) (matrixDomain m n) :=
  (F.sep_members _ _ _).mpr ⟨(FiniteFunction.cart2_members _ _ _).mpr ⟨a,ha,b,hb,rfl⟩,True.intro⟩

structure MatrixTraceObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β

noncomputable def matrixTraceRawValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a n : M.Value) : ℂ :=
  finiteAggregateValue false (closedRangeValue (M.number 1) n)
    (fun k => NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 k k)))

noncomputable def matrixTraceValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β) : ℂ :=
  matrixTraceRawValue a (denote n)

noncomputable instance matrixTraceRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixTraceObj (M := M) α β) where
  wd p := In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := M.number (matrixTraceValue (denote p.matrix) p.order)
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_,rfl⟩)

noncomputable def matrixTrace {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixTraceObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha⟩

theorem matrixTraceInC {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixTraceObj (M := M) α β)) : In p C :=
  (M.complex_members _).mpr ⟨_,rfl⟩

theorem matrixTraceInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixTraceObj (M := M) α β))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) : In p R := by
  apply finiteAggregateValueMember false _ _ .real (matrixIndexFinite p.val.order p.wd.1)
  intro k hk
  have hr := F.call_mem _ _ _ _ ha (matrixDomain_pair p.val.order p.val.order k k hk hk)
  rw [← NativeBridge.complexValue_spec _ (M.real_subset_complex _ hr)]
  exact hr

theorem matrixTraceFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixTraceObj (M := M) α β)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.order)
    (hb : f.val.bodyValue = fun k => F.callValue (denote p.val.matrix) (FiniteFunction.pack2 k k)) :
    denote p = M.number (finiteAggregateValue false (matrixIndexValue p.val.order)
      (fun k => NativeBridge.complexValue (F.callValue (denote f) k))) := by
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro k hk
  have hd : M.mem k f.val.signature.domain := hD ▸ (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have h := F.call_graphValue _ _ _ f.wd k hd
  change F.callValue (denote f) k = f.val.bodyValue k at h
  rw [h, hb]
end Litex

namespace Litex
structure MatrixMultiplyObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) (ε : Type r) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] [Representation M ε] where
  left : Obj (M := M) α
  right : Obj (M := M) β
  rows : Obj (M := M) γ
  inner : Obj (M := M) δ
  cols : Obj (M := M) ε

noncomputable def matrixMultiplyTerm {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b q k : M.Value) : M.Value :=
  M.mulValue (F.callValue a (FiniteFunction.pack2 (FiniteFunction.unpack2 q).1 k))
    (F.callValue b (FiniteFunction.pack2 k (FiniteFunction.unpack2 q).2))

noncomputable def matrixMultiplyRawBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b n q : M.Value) : M.Value :=
  M.number (finiteAggregateValue false (closedRangeValue (M.number 1) n)
    (fun k => NativeBridge.complexValue (F.callValue
      (F.graphValue (F.sepValue (closedRangeValue (M.number 1) n) (fun _ => True))
        (M.standard .complex) (matrixMultiplyTerm a b q)) k)))

noncomputable def matrixMultiplyBody {M : Semantics.{u}} [F : FunctionSemantics M]
    {δ : Type t} [Representation M δ] (a b : M.Value) (n : Obj (M := M) δ) (q : M.Value) : M.Value :=
  matrixMultiplyRawBody a b (denote n) q

noncomputable instance matrixMultiplyRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε] :
    Representation M (MatrixMultiplyObj (M := M) α β γ δ ε) where
  wd p := In p.rows N ∧ In p.inner N ∧ In p.cols N ∧
    M.mem (denote p.left) (F.fnSetValue (matrixDomain p.rows p.inner) (M.standard .complex)) ∧
    M.mem (denote p.right) (F.fnSetValue (matrixDomain p.inner p.cols) (M.standard .complex))
  denote p := F.graphValue (matrixDomain p.rows p.cols) (M.standard .complex)
    (matrixMultiplyBody (denote p.left) (denote p.right) p.inner)
  wd_isSet _ := M.member_isSet (F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩))

noncomputable def matrixMultiply {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m : Obj (M := M) γ) (k : Obj (M := M) δ) (n : Obj (M := M) ε)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain k n) (M.standard .complex))) :
    Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε) := ⟨⟨a,b,m,k,n⟩,hm,hk,hn,ha,hb⟩

theorem matrixMultiplyInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε)) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .complex)) :=
  F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩)

theorem matrixMultiplyCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) q = matrixMultiplyBody (denote p.val.left) (denote p.val.right) p.val.inner q :=
  F.call_graphValue _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩) q hq

theorem matrixMultiplyInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε))
    (ha : M.mem (denote p.val.left) (F.fnSetValue (matrixDomain p.val.rows p.val.inner) (M.standard .real)))
    (hb : M.mem (denote p.val.right) (F.fnSetValue (matrixDomain p.val.inner p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (matrixMultiplyInFnSet p)
  intro q hq
  rw [matrixMultiplyCall p q hq]
  have hr := (F.sep_members _ _ _).mp (matrixDomain_first p.val.rows p.val.cols q hq)
  have hc := (F.sep_members _ _ _).mp (matrixDomain_second p.val.rows p.val.cols q hq)
  have ht : ∀ k, M.mem k (finiteSeqDomain p.val.inner) →
      M.mem (matrixMultiplyTerm (denote p.val.left) (denote p.val.right) q k) (M.standard .real) := by
    intro k hk
    have hi := (F.sep_members _ _ _).mp hk
    exact mulValuesInReal
      (F.call_mem _ _ _ _ ha (matrixDomain_pair p.val.rows p.val.inner _ _ hr.1 hi.1))
      (F.call_mem _ _ _ _ hb (matrixDomain_pair p.val.inner p.val.cols _ _ hi.1 hc.1))
  apply finiteAggregateValueMember false _ _ .real (matrixIndexFinite p.val.inner p.wd.2.1)
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.inner) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have he := F.call_graphValue (finiteSeqDomain p.val.inner) (M.standard .complex)
    (matrixMultiplyTerm (denote p.val.left) (denote p.val.right) q)
    (fun z hz => M.real_subset_complex _ (ht z hz)) k hd
  change M.mem (M.number (NativeBridge.complexValue (F.callValue
    (F.graphValue (finiteSeqDomain p.val.inner) (M.standard .complex)
      (matrixMultiplyTerm (denote p.val.left) (denote p.val.right) q)) k))) (M.standard .real)
  rw [he, ← NativeBridge.complexValue_spec _ (M.real_subset_complex _ (ht k hd))]
  exact ht k hd

theorem matrixMultiply_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.rows p.val.cols)
    (hbody : g.val.bodyValue = matrixMultiplyBody (denote p.val.left) (denote p.val.right) p.val.inner) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.rows p.val.cols .complex) g.val.signature
    (matrixMultiplyInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixMultiplyCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
structure MatrixApplyObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  matrix : Obj (M := M) α
  vector : Obj (M := M) β
  rows : Obj (M := M) γ
  cols : Obj (M := M) δ

noncomputable def matrixApplyTerm {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b q k : M.Value) : M.Value :=
  M.mulValue (F.callValue a (FiniteFunction.pack2 q k)) (F.callValue b k)
noncomputable def matrixApplyBody {M : Semantics.{u}} [F : FunctionSemantics M]
    {δ : Type t} [Representation M δ] (a b : M.Value) (n : Obj (M := M) δ) (q : M.Value) : M.Value :=
  M.number (finiteAggregateValue false (matrixIndexValue n)
    (fun k => NativeBridge.complexValue (F.callValue
      (F.graphValue (finiteSeqDomain n) (M.standard .complex) (matrixApplyTerm a b q)) k)))
noncomputable def matrixApplySignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (rows : Obj (M := M) α) (S : StandardSetValue) : FunctionSignature M :=
  ⟨finiteSeqDomain rows,finiteSeqDomain_isSet rows,M.standard S,M.standard_isSet S⟩

noncomputable instance matrixApplyRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixApplyObj (M := M) α β γ δ) where
  wd p := In p.rows N ∧ In p.cols N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.rows p.cols) (M.standard .complex)) ∧
    M.mem (denote p.vector) (F.fnSetValue (finiteSeqDomain p.cols) (M.standard .complex))
  denote p := F.graphValue (finiteSeqDomain p.rows) (M.standard .complex)
    (matrixApplyBody (denote p.matrix) (denote p.vector) p.cols)
  wd_isSet _ := M.member_isSet (F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩))
noncomputable def matrixApply {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (MatrixApplyObj (M := M) α β γ δ) := ⟨⟨a,b,m,n⟩,hm,hn,ha,hb⟩
theorem matrixApplyInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ)) :
    In p (fnSet (matrixApplySignature p.val.rows .complex)) :=
  F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩)
theorem matrixApplyCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ)) (q : M.Value)
    (hq : M.mem q (finiteSeqDomain p.val.rows)) :
    F.callValue (denote p) q = matrixApplyBody (denote p.val.matrix) (denote p.val.vector) p.val.cols q :=
  F.call_graphValue _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩) q hq

theorem matrixApplyInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real)))
    (hb : M.mem (denote p.val.vector) (F.fnSetValue (finiteSeqDomain p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixApplySignature p.val.rows .real)) := by
  apply F.fnSet_of_returns (matrixApplyInFnSet p)
  intro q hq
  rw [matrixApplyCall p q hq]
  have hr := (F.sep_members _ _ _).mp hq
  have ht : ∀ k, M.mem k (finiteSeqDomain p.val.cols) →
      M.mem (matrixApplyTerm (denote p.val.matrix) (denote p.val.vector) q k) (M.standard .real) := by
    intro k hk
    have hi := (F.sep_members _ _ _).mp hk
    exact mulValuesInReal
      (F.call_mem _ _ _ _ ha (matrixDomain_pair p.val.rows p.val.cols _ _ hr.1 hi.1))
      (F.call_mem _ _ _ _ hb hk)
  apply finiteAggregateValueMember false _ _ .real (matrixIndexFinite p.val.cols p.wd.2.1)
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.cols) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have he := F.call_graphValue (finiteSeqDomain p.val.cols) (M.standard .complex)
    (matrixApplyTerm (denote p.val.matrix) (denote p.val.vector) q)
    (fun z hz => M.real_subset_complex _ (ht z hz)) k hd
  rw [he, ← NativeBridge.complexValue_spec _ (M.real_subset_complex _ (ht k hd))]
  exact ht k hd

theorem matrixApply_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = finiteSeqDomain p.val.rows)
    (hbody : g.val.bodyValue = matrixApplyBody (denote p.val.matrix) (denote p.val.vector) p.val.cols) : Same p g := by
  apply functionExtOnDomain p g (matrixApplySignature p.val.rows .complex) g.val.signature
    (matrixApplyInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixApplyCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
structure FiniteInnerProductObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  left : Obj (M := M) α
  right : Obj (M := M) β
  dimension : Obj (M := M) γ
noncomputable def finiteInnerProductTerm {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b k : M.Value) : M.Value :=
  M.mulValue (complexUnaryValue (fun z : ℂ => star z) (F.callValue a k)) (F.callValue b k)
noncomputable def finiteInnerProductRawValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b n : M.Value) : ℂ :=
  finiteAggregateValue false (closedRangeValue (M.number 1) n)
    (fun k => NativeBridge.complexValue (finiteInnerProductTerm a b k))
noncomputable def finiteInnerProductValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {γ : Type x} [Representation M γ] (a b : M.Value) (n : Obj (M := M) γ) : ℂ :=
  finiteInnerProductRawValue a b (denote n)
noncomputable instance finiteInnerProductRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (FiniteInnerProductObj (M := M) α β γ) where
  wd p := In p.dimension N ∧
    M.mem (denote p.left) (F.fnSetValue (finiteSeqDomain p.dimension) (M.standard .complex)) ∧
    M.mem (denote p.right) (F.fnSetValue (finiteSeqDomain p.dimension) (M.standard .complex))
  denote p := M.number (finiteInnerProductValue (denote p.left) (denote p.right) p.dimension)
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_,rfl⟩)
noncomputable def finiteInnerProduct {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (FiniteInnerProductObj (M := M) α β γ) := ⟨⟨a,b,n⟩,hn,ha,hb⟩
theorem finiteInnerProductInC {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ)) : In p C :=
  (M.complex_members _).mpr ⟨_,rfl⟩
theorem finiteInnerProductInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ))
    (ha : M.mem (denote p.val.left) (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .real)))
    (hb : M.mem (denote p.val.right) (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .real))) : In p R := by
  apply finiteAggregateValueMember false _ _ .real (matrixIndexFinite p.val.dimension p.wd.1)
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.dimension) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have hr := mulValuesInReal (conjugateValueInReal _ (F.call_mem _ _ _ _ ha hd)) (F.call_mem _ _ _ _ hb hd)
  unfold finiteInnerProductTerm
  rw [← NativeBridge.complexValue_spec _ (M.real_subset_complex _ hr)]
  exact hr
theorem finiteInnerProductFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.dimension)
    (hb : f.val.bodyValue = finiteInnerProductTerm (denote p.val.left) (denote p.val.right)) :
    denote p = M.number (finiteAggregateValue false (matrixIndexValue p.val.dimension)
      (fun k => NativeBridge.complexValue (F.callValue (denote f) k))) := by
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro k hk
  have hd : M.mem k f.val.signature.domain := hD ▸ (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have h := F.call_graphValue _ _ _ f.wd k hd
  change F.callValue (denote f) k = f.val.bodyValue k at h
  rw [h,hb]
end Litex

namespace Litex
theorem finiteInnerProductConjugateSymmetry {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ)) :
    denote p = complexUnaryValue (fun z : ℂ => star z)
      (M.number (finiteInnerProductValue (denote p.val.right) (denote p.val.left) p.val.dimension)) := by
  classical
  change M.number (finiteInnerProductValue (denote p.val.left) (denote p.val.right) p.val.dimension) = _
  rw [complexUnaryValue_number]
  apply congrArg M.number
  unfold finiteInnerProductValue finiteInnerProductRawValue
  trans finiteAggregateValue false (matrixIndexValue p.val.dimension)
    (fun k => star (NativeBridge.complexValue (finiteInnerProductTerm (denote p.val.right) (denote p.val.left) k)))
  · apply finiteAggregateValue_congr
    intro k hk
    have hd : M.mem k (finiteSeqDomain p.val.dimension) :=
      (F.sep_members _ _ _).mpr ⟨hk, True.intro⟩
    obtain ⟨a, ha⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ p.wd.2.1 hd)
    obtain ⟨b, hb⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ p.wd.2.2 hd)
    unfold finiteInnerProductTerm
    simp only [ha, hb, complexUnaryValue_number, M.mul_numbers,
      NativeBridge.complexValue_number, star_mul, star_star, mul_comm]
  · change _ = star (finiteAggregateValue false (matrixIndexValue p.val.dimension)
      (fun k => NativeBridge.complexValue (finiteInnerProductTerm (denote p.val.right) (denote p.val.left) k)))
    simp only [finiteAggregateValue, dif_pos (matrixIndexFinite p.val.dimension p.wd.1),
      Bool.false_eq_true, ↓reduceIte]
    exact (map_sum (starRingEnd ℂ) _ _).symm

end Litex

-- Finite Euclidean and Frobenius norms retain their source WD.
namespace Litex
theorem finiteRealSumNonnegative {M : Semantics.{u}} (A : M.Value) (f : M.Value → ℝ)
    (hf : (memberSet A).Finite) (h : ∀ x, M.mem x A → 0 ≤ f x) :
    ∃ r : ℝ, 0 ≤ r ∧ finiteAggregateValue false A (fun x => (f x : ℂ)) = (r : ℂ) := by
  classical
  refine ⟨∑ x ∈ hf.toFinset, f x, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun x hx => h x (hf.mem_toFinset.mp hx))
  · simp only [finiteAggregateValue, dif_pos hf, Bool.false_eq_true, ↓reduceIte]
    exact (map_sum Complex.ofRealHom f hf.toFinset).symm

theorem finiteMagnitudeSquareSumNonnegative {M : Semantics.{u}} (A : M.Value)
    (f : M.Value → ℂ) (hf : (memberSet A).Finite) :
    ∃ r : ℝ, 0 ≤ r ∧ finiteAggregateValue false A (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) = (r : ℂ) :=
  finiteRealSumNonnegative A (fun x => ‖f x‖ ^ 2) hf (fun x _ => sq_nonneg (‖f x‖))

theorem finiteNestedMagnitudeSquareSumNonnegative {M : Semantics.{u}}
    (A B : M.Value) (f : M.Value → M.Value → ℂ)
    (ha : (memberSet A).Finite) (hb : (memberSet B).Finite) :
    ∃ r : ℝ, 0 ≤ r ∧ finiteAggregateValue false A
      (fun x => finiteAggregateValue false B (fun y => ((‖f x y‖ ^ 2 : ℝ) : ℂ))) = (r : ℂ) := by
  classical
  have rows := fun x => finiteMagnitudeSquareSumNonnegative B (f x) hb
  choose r hr he using rows
  have same := finiteAggregateValue_congr false A
    (fun x => finiteAggregateValue false B (fun y => ((‖f x y‖ ^ 2 : ℝ) : ℂ)))
    (fun x => (r x : ℂ)) (fun x _ => he x)
  obtain ⟨s,hs,eq⟩ := finiteRealSumNonnegative A r ha (fun x _ => hr x)
  exact ⟨s,hs,same.trans eq⟩

theorem finiteMagnitudeSquareSumWD {M : Semantics.{u}} (A : M.Value)
    (f : M.Value → ℂ) (hf : (memberSet A).Finite) :
    In (number (M := M) (finiteAggregateValue false A (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)))) R ∧
    Le (number 0) (number (M := M) (finiteAggregateValue false A (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)))) := by
  obtain ⟨r,hr,eq⟩ := finiteMagnitudeSquareSumNonnegative A f hf
  rw [eq]
  exact ⟨NativeBridge.numberInR r, 0, r, rfl, rfl, hr⟩

noncomputable def magnitudeSquareValue {M : Semantics.{u}} (a : M.Value) : M.Value :=
  M.powValue (complexUnaryValue (fun z : ℂ => (‖z‖ : ℂ)) a) (M.number (2 : ℂ))

theorem magnitudeSquareValue_number {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .complex)) :
    magnitudeSquareValue a = M.number ((‖NativeBridge.complexValue a‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨z,rfl⟩ := (M.complex_members _).mp ha
  unfold magnitudeSquareValue
  rw [complexUnaryValue_number, NativeBridge.complexValue_number]
  change M.powValue (M.number (‖z‖ : ℂ)) (M.number ((2 : ℕ) : ℂ)) = _
  rw [M.pow_numbers_nat, Complex.ofReal_pow]

theorem magnitudeSquareValueInReal {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .complex)) : M.mem (magnitudeSquareValue a) (M.standard .real) := by
  rw [magnitudeSquareValue_number a ha]
  exact (M.real_members _).mpr ⟨_,rfl⟩

theorem sqrtValueRealOfNonnegative {M : Semantics.{u}} (z : ℂ)
    (h : ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)) :
    M.mem (sqrtValue (M.number z)) (M.standard .real) := by
  obtain ⟨r,_,rfl⟩ := h
  rw [sqrtValue_number]
  exact (M.real_members _).mpr ⟨_,rfl⟩

theorem sqrtValueSquareOfNonnegative {M : Semantics.{u}} (z : ℂ)
    (h : ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)) :
    M.powValue (sqrtValue (M.number z)) (M.number (2 : ℂ)) = M.number z := by
  obtain ⟨r,hr,rfl⟩ := h
  rw [sqrtValue_number]
  change M.powValue (M.number ((Real.sqrt r : ℝ) : ℂ)) (M.number ((2 : ℕ) : ℂ)) = _
  rw [M.pow_numbers_nat, ← Complex.ofReal_pow, Real.sq_sqrt hr]

structure EuclideanNormObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  vector : Obj (M := M) α
  dimension : Obj (M := M) β
noncomputable def euclideanNormSum {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β) : ℂ :=
  finiteAggregateValue false (matrixIndexValue n)
    (fun k => ((‖NativeBridge.complexValue (F.callValue a k)‖ ^ 2 : ℝ) : ℂ))
noncomputable instance euclideanNormRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (EuclideanNormObj (M := M) α β) where
  wd p := In p.dimension N ∧
    M.mem (denote p.vector) (F.fnSetValue (finiteSeqDomain p.dimension) (M.standard .complex))
  denote p := sqrtValue (M.number (euclideanNormSum (denote p.vector) p.dimension))
  wd_isSet {p} h := M.member_isSet (sqrtValueRealOfNonnegative _
    (finiteMagnitudeSquareSumNonnegative _ _ (matrixIndexFinite p.dimension h.1)))
noncomputable def euclideanNorm {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (EuclideanNormObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha⟩
theorem euclideanNormInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) : In p R :=
  sqrtValueRealOfNonnegative _
    (finiteMagnitudeSquareSumNonnegative _ _ (matrixIndexFinite p.val.dimension p.wd.1))
theorem euclideanNormNonnegative {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) : Le (number 0) p := by
  obtain ⟨r,_,hr⟩ := finiteMagnitudeSquareSumNonnegative (matrixIndexValue p.val.dimension)
    (fun k => NativeBridge.complexValue (F.callValue (denote p.val.vector) k)) (matrixIndexFinite p.val.dimension p.wd.1)
  refine ⟨0,Real.sqrt r,rfl,?_,Real.sqrt_nonneg r⟩
  change sqrtValue (M.number (euclideanNormSum _ _)) = _
  rw [show euclideanNormSum (denote p.val.vector) p.val.dimension = (r : ℂ) from hr, sqrtValue_number]
theorem euclideanNormSquare {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) :
    M.powValue (denote p) (M.number (2 : ℂ)) = M.number (euclideanNormSum (denote p.val.vector) p.val.dimension) :=
  sqrtValueSquareOfNonnegative _
    (finiteMagnitudeSquareSumNonnegative _ _ (matrixIndexFinite p.val.dimension p.wd.1))

theorem euclideanNormSumFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.dimension)
    (hb : f.val.bodyValue = fun k => magnitudeSquareValue (F.callValue (denote p.val.vector) k)) :
    euclideanNormSum (denote p.val.vector) p.val.dimension =
      finiteAggregateValue false (matrixIndexValue p.val.dimension)
        (fun k => NativeBridge.complexValue (F.callValue (denote f) k)) := by
  apply finiteAggregateValue_congr
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.dimension) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have he := F.call_graphValue _ _ _ f.wd k (hD ▸ hd)
  change F.callValue (denote f) k = f.val.bodyValue k at he
  rw [he,hb]
  dsimp only
  rw [magnitudeSquareValue_number _ (F.call_mem _ _ _ _ p.wd.2 hd), NativeBridge.complexValue_number]

theorem euclideanNormFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.dimension)
    (hb : f.val.bodyValue = fun k => magnitudeSquareValue (F.callValue (denote p.val.vector) k)) :
    denote p = sqrtValue (M.number (finiteAggregateValue false (matrixIndexValue p.val.dimension)
      (fun k => NativeBridge.complexValue (F.callValue (denote f) k)))) :=
  congrArg (fun z => sqrtValue (M.number z)) (euclideanNormSumFormula p f hD hb)

theorem euclideanNormSquareInner {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) :
    M.powValue (denote p) (M.number (2 : ℂ)) =
      M.number (finiteInnerProductValue (denote p.val.vector) (denote p.val.vector) p.val.dimension) := by
  apply (euclideanNormSquare p).trans
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.dimension) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  obtain ⟨z,hz⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ p.wd.2 hd)
  unfold finiteInnerProductTerm
  rw [hz,complexUnaryValue_number,M.mul_numbers,NativeBridge.complexValue_number,NativeBridge.complexValue_number]
  change ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z
  rw [mul_comm (star z) z, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

structure FrobeniusNormObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ
noncomputable def frobeniusNormRawSum {M : Semantics.{u}} [F : FunctionSemantics M]
    (a m n : M.Value) : ℂ :=
  finiteAggregateValue false (closedRangeValue (M.number 1) m) (fun r =>
    finiteAggregateValue false (closedRangeValue (M.number 1) n) (fun c =>
      ((‖NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 r c))‖ ^ 2 : ℝ) : ℂ)))
noncomputable def frobeniusNormSum {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} {γ : Type x} [Representation M β] [Representation M γ]
    (a : M.Value) (m : Obj (M := M) β) (n : Obj (M := M) γ) : ℂ :=
  frobeniusNormRawSum a (denote m) (denote n)
noncomputable instance frobeniusNormRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (FrobeniusNormObj (M := M) α β γ) where
  wd p := In p.rows N ∧ In p.cols N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.rows p.cols) (M.standard .complex))
  denote p := sqrtValue (M.number (frobeniusNormSum (denote p.matrix) p.rows p.cols))
  wd_isSet {p} h := M.member_isSet (sqrtValueRealOfNonnegative _
    (finiteNestedMagnitudeSquareSumNonnegative _ _ _
      (matrixIndexFinite p.rows h.1) (matrixIndexFinite p.cols h.2.1)))
noncomputable def frobeniusNorm {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (FrobeniusNormObj (M := M) α β γ) := ⟨⟨a,m,n⟩,hm,hn,ha⟩
theorem frobeniusNormInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) : In p R :=
  sqrtValueRealOfNonnegative _ (finiteNestedMagnitudeSquareSumNonnegative _ _ _
    (matrixIndexFinite p.val.rows p.wd.1) (matrixIndexFinite p.val.cols p.wd.2.1))
theorem frobeniusNormNonnegative {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) : Le (number 0) p := by
  obtain ⟨r,_,hr⟩ := finiteNestedMagnitudeSquareSumNonnegative
    (matrixIndexValue p.val.rows) (matrixIndexValue p.val.cols)
    (fun i j => NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 i j)))
    (matrixIndexFinite p.val.rows p.wd.1) (matrixIndexFinite p.val.cols p.wd.2.1)
  refine ⟨0,Real.sqrt r,rfl,?_,Real.sqrt_nonneg r⟩
  change sqrtValue (M.number (frobeniusNormSum _ _ _)) = _
  rw [show frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols = (r : ℂ) from hr, sqrtValue_number]
theorem frobeniusNormSquare {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) :
    M.powValue (denote p) (M.number (2 : ℂ)) =
      M.number (frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols) :=
  sqrtValueSquareOfNonnegative _ (finiteNestedMagnitudeSquareSumNonnegative _ _ _
    (matrixIndexFinite p.val.rows p.wd.1) (matrixIndexFinite p.val.cols p.wd.2.1))

-- The source row function calls the checked column graph inside its finite sum.
noncomputable def frobeniusNormRowValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {γ : Type x} [Representation M γ] (a : M.Value) (n : Obj (M := M) γ)
    (row : M.Value) : M.Value :=
  M.number (finiteAggregateValue false (matrixIndexValue n) (fun col =>
    NativeBridge.complexValue (F.callValue
      (F.graphValue (finiteSeqDomain n) (M.standard .real)
        (fun col => magnitudeSquareValue (F.callValue a (FiniteFunction.pack2 row col)))) col)))
theorem frobeniusNormRowValue_eq {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ))
    (row : M.Value) (hr : M.mem row (matrixIndexValue p.val.rows)) :
    frobeniusNormRowValue (denote p.val.matrix) p.val.cols row =
      M.number (finiteAggregateValue false (matrixIndexValue p.val.cols) (fun col =>
        ((‖NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 row col))‖ ^ 2 : ℝ) : ℂ))) := by
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro col hc
  have member := fun c hc => F.call_mem _ _ _ _ p.wd.2.2
    (matrixDomain_pair p.val.rows p.val.cols row c hr hc)
  have ret : ∀ c, M.mem c (finiteSeqDomain p.val.cols) →
      M.mem (magnitudeSquareValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 row c))) (M.standard .real) := by
    intro c hc
    exact magnitudeSquareValueInReal _ (member c ((F.sep_members _ _ _).mp hc).1)
  rw [F.call_graphValue _ _ _ ret col ((F.sep_members _ _ _).mpr ⟨hc,True.intro⟩)]
  rw [magnitudeSquareValue_number _ (member col hc), NativeBridge.complexValue_number]
theorem frobeniusNormSumFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.rows)
    (hb : f.val.bodyValue = fun row => frobeniusNormRowValue (denote p.val.matrix) p.val.cols row) :
    frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols =
      finiteAggregateValue false (matrixIndexValue p.val.rows)
        (fun row => NativeBridge.complexValue (F.callValue (denote f) row)) := by
  apply finiteAggregateValue_congr
  intro row hr
  have hd : M.mem row (finiteSeqDomain p.val.rows) := (F.sep_members _ _ _).mpr ⟨hr,True.intro⟩
  have he := F.call_graphValue _ _ _ f.wd row (hD ▸ hd)
  change F.callValue (denote f) row = f.val.bodyValue row at he
  rw [he,hb]
  dsimp only
  rw [frobeniusNormRowValue_eq p row hr, NativeBridge.complexValue_number]
  rfl
theorem frobeniusNormFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.rows)
    (hb : f.val.bodyValue = fun row => frobeniusNormRowValue (denote p.val.matrix) p.val.cols row) :
    denote p = sqrtValue (M.number (finiteAggregateValue false (matrixIndexValue p.val.rows)
      (fun row => NativeBridge.complexValue (F.callValue (denote f) row)))) :=
  congrArg (fun z => sqrtValue (M.number z)) (frobeniusNormSumFormula p f hD hb)
end Litex

-- Determinants observe the original finite matrix on one-based source indices.
namespace Litex

theorem matrixIndexOfFin {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N)
    (i : Fin (NativeBridge.naturalValue (denote n))) :
    M.mem (FiniteFunction.index i) (matrixIndexValue n) := by
  change In (number ((i.val + 1 : ℕ) : ℂ))
    (closedRange (number 1) n (NativeBridge.numberInZOfEq 1 1 (by norm_num)) (naturalToInteger n hn))
  apply inClosedRangeOfDenote _ _ _ _ _ 1
    (NativeBridge.naturalValue (denote n)) ((i.val + 1 : ℕ) : ℤ)
  · change M.number 1 = M.number ((1 : ℤ) : ℂ)
    norm_num
  · simpa only [Complex.ofReal_intCast, Int.cast_natCast] using NativeBridge.naturalValue_spec (denote n) hn
  · change M.number ((i.val + 1 : ℕ) : ℂ) = M.number (((i.val + 1 : ℕ) : ℤ) : ℂ)
    norm_num
  · exact_mod_cast (Nat.succ_le_succ (Nat.zero_le i.val))
  · exact_mod_cast (Nat.succ_le_of_lt i.isLt)

theorem matrixIndexNaturalNumber {M : Semantics.{u}} [FunctionSemantics M]
    (n k : ℕ) (hpos : 1 ≤ k) (hbound : k ≤ n) :
    M.mem (M.number (k : ℂ)) (matrixIndexValue (number (M := M) (n : ℂ))) := by
  let i : Fin n := ⟨k - 1, by omega⟩
  have h := matrixIndexOfFin (number (M := M) (n : ℂ)) (NativeBridge.numberInN n)
    (Fin.cast (NativeBridge.naturalValue_number (M := M) n).symm i)
  simpa [FiniteFunction.index, i, Nat.sub_add_cancel hpos] using h

noncomputable def matrixComplexOn {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (m n : ℕ) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j)))
noncomputable def matrixComplexValue {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : M.Value) (m : Obj (M := M) α) (n : Obj (M := M) β) :
    Matrix (Fin (NativeBridge.naturalValue (denote m))) (Fin (NativeBridge.naturalValue (denote n))) ℂ :=
  matrixComplexOn a _ _
noncomputable def matrixDeterminantValue {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α) : M.Value :=
  M.number (matrixComplexValue a n n).det
structure MatrixDeterminantObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β
noncomputable instance matrixDeterminantRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixDeterminantObj (M := M) α β) where
  wd p := In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := matrixDeterminantValue (denote p.matrix) p.order
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_,rfl⟩)
noncomputable def matrixDeterminant {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixDeterminantObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha⟩
theorem matrixDeterminantInC {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDeterminantObj (M := M) α β)) : In p C :=
  (M.complex_members _).mpr ⟨_,rfl⟩
theorem matrixDeterminantInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDeterminantObj (M := M) α β))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) : In p R := by
  let a := matrixComplexValue (denote p.val.matrix) p.val.order p.val.order
  have real : ∀ i j, ((a i j).re : ℂ) = a i j := by
    intro i j
    obtain ⟨r,hr⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ ha
      (matrixDomain_pair _ _ _ _ (matrixIndexOfFin _ p.wd.1 i) (matrixIndexOfFin _ p.wd.1 j)))
    change ((NativeBridge.complexValue _).re : ℂ) = NativeBridge.complexValue _
    rw [hr, NativeBridge.complexValue_number, Complex.ofReal_re]
  apply (M.real_members _).mpr
  refine ⟨(Matrix.det (fun i j => (a i j).re)), ?_⟩
  change M.number a.det = M.number (Complex.ofRealHom (Matrix.det (fun i j => (a i j).re)))
  apply congrArg M.number
  rw [Complex.ofRealHom.map_det]
  congr 1
  ext i j
  exact (real i j).symm

theorem matrixComplexValue_identity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N) :
    matrixComplexValue (denote (identityMatrix n hn)) n n = 1 := by
  classical
  ext i j
  unfold matrixComplexValue matrixComplexOn
  rw [identityMatrixCall _ _ (matrixDomain_pair _ _ _ _ (matrixIndexOfFin n hn i) (matrixIndexOfFin n hn j))]
  simp only [matrixIdentityBody, FiniteFunction.unpack_pack2, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    rw [matrixIdentityEntrySelf, NativeBridge.complexValue_number, if_pos rfl]
  · rw [matrixIdentityEntryDifferent _ _ (fun eq => h (FiniteFunction.index_injective eq)), NativeBridge.complexValue_number, if_neg h]
theorem matrixDeterminantIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N) :
    matrixDeterminantValue (denote (identityMatrix n hn)) n = M.number 1 := by
  unfold matrixDeterminantValue
  rw [matrixComplexValue_identity, Matrix.det_one]

theorem matrixComplexValue_transpose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ)) :
    matrixComplexValue (denote p) p.val.cols p.val.rows =
      (matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols).transpose := by
  ext i j
  unfold matrixComplexValue matrixComplexOn
  rw [transposeCall _ _ (matrixDomain_pair _ _ _ _ (matrixIndexOfFin _ p.wd.2.1 i) (matrixIndexOfFin _ p.wd.1 j))]
  simp only [matrixTransposeBody, FiniteFunction.unpack_pack2, Matrix.transpose_apply]
theorem matrixDeterminantTranspose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    matrixDeterminantValue (denote (transpose a n n hn hn ha)) n = matrixDeterminantValue (denote a) n := by
  unfold matrixDeterminantValue
  apply congrArg M.number
  exact (congrArg Matrix.det (matrixComplexValue_transpose (transpose a n n hn hn ha))).trans (Matrix.det_transpose _)

theorem matrixComplexValue_adjoint {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ)) :
    matrixComplexValue (denote p) p.val.cols p.val.rows =
      (matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols).conjTranspose := by
  ext i j
  unfold matrixComplexValue matrixComplexOn
  rw [conjugateTransposeCall _ _ (matrixDomain_pair _ _ _ _ (matrixIndexOfFin _ p.wd.2.1 i) (matrixIndexOfFin _ p.wd.1 j))]
  simp only [matrixConjugateTransposeBody, matrixTransposeBody, FiniteFunction.unpack_pack2, Matrix.conjTranspose_apply]
  obtain ⟨z,hz⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ p.wd.2.2
    (matrixDomain_pair _ _ _ _ (matrixIndexOfFin _ p.wd.1 j) (matrixIndexOfFin _ p.wd.2.1 i)))
  rw [hz, complexUnaryValue_number, NativeBridge.complexValue_number, NativeBridge.complexValue_number]
theorem matrixDeterminantAdjoint {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    matrixDeterminantValue (denote (conjugateTranspose a n n hn hn ha)) n =
      complexUnaryValue (fun z : ℂ => star z) (matrixDeterminantValue (denote a) n) := by
  unfold matrixDeterminantValue
  rw [complexUnaryValue_number]
  apply congrArg M.number
  exact (congrArg Matrix.det (matrixComplexValue_adjoint (conjugateTranspose a n n hn hn ha))).trans (Matrix.det_conjTranspose _)

noncomputable def matrixEntryValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (i j : ℕ) : M.Value :=
  F.callValue a (FiniteFunction.pack2 (M.number (i : ℂ)) (M.number (j : ℂ)))
theorem matrixDeterminantValue_number {M : Semantics.{u}} [FunctionSemantics M]
    (a : M.Value) (n : ℕ) :
    matrixDeterminantValue a (number (n : ℂ)) = M.number (matrixComplexOn a n n).det := by
  unfold matrixDeterminantValue matrixComplexValue
  change M.number (matrixComplexOn a (NativeBridge.naturalValue (M.number (n : ℂ)))
    (NativeBridge.naturalValue (M.number (n : ℂ)))).det = _
  rw [NativeBridge.naturalValue_number]
theorem matrixDeterminantZero {M : Semantics.{u}} [FunctionSemantics M] (a : M.Value) :
    matrixDeterminantValue a (number 0) = M.number 1 := by
  have h := matrixDeterminantValue_number a 0
  simp only [Nat.cast_zero] at h
  rw [h, Matrix.det_fin_zero]
theorem matrixDeterminantOne {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 1) (number 1)) (M.standard .complex))) :
    matrixDeterminantValue a (number 1) = matrixEntryValue a 1 1 := by
  have h := matrixDeterminantValue_number a 1
  simp only [Nat.cast_one] at h
  rw [h, Matrix.det_fin_one]
  simp only [matrixComplexOn, matrixEntryValue, FiniteFunction.index, Fin.val_zero, zero_add, Nat.cast_one]
  symm
  apply NativeBridge.complexValue_spec
  have h1 : M.mem (M.number 1) (matrixIndexValue (number 1)) :=
    by simpa only [Nat.cast_one] using (matrixIndexNaturalNumber (M := M) 1 1 (by omega) (by omega))
  exact F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h1 h1)
theorem matrixDeterminantTwo {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixDeterminantValue a (number 2) =
      M.subValue (M.mulValue (matrixEntryValue a 1 1) (matrixEntryValue a 2 2))
        (M.mulValue (matrixEntryValue a 1 2) (matrixEntryValue a 2 1)) := by
  have h1 : M.mem (M.number 1) (matrixIndexValue (number 2)) :=
    by simpa only [Nat.cast_one, Nat.cast_ofNat] using (matrixIndexNaturalNumber (M := M) 2 1 (by omega) (by omega))
  have h2 : M.mem (M.number 2) (matrixIndexValue (number 2)) :=
    by simpa only [Nat.cast_one, Nat.cast_ofNat] using (matrixIndexNaturalNumber (M := M) 2 2 (by omega) (by omega))
  have h11 := NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h1 h1))
  have h12 := NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h1 h2))
  have h21 := NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h2 h1))
  have h22 := NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h2 h2))
  have h := matrixDeterminantValue_number a 2
  simp only [Nat.cast_ofNat] at h
  rw [h, Matrix.det_fin_two]
  change M.number (NativeBridge.complexValue (matrixEntryValue a 1 1) * NativeBridge.complexValue (matrixEntryValue a 2 2) -
    NativeBridge.complexValue (matrixEntryValue a 1 2) * NativeBridge.complexValue (matrixEntryValue a 2 1)) = _
  simp only [matrixEntryValue, Nat.cast_one, Nat.cast_ofNat] at ⊢
  exact (M.sub_numbers _ _).symm.trans (congrArg₂ M.subValue
    ((M.mul_numbers _ _).symm.trans (congrArg₂ M.mulValue h11.symm h22.symm))
    ((M.mul_numbers _ _).symm.trans (congrArg₂ M.mulValue h12.symm h21.symm)))
end Litex

namespace Litex
noncomputable def matrixPowerRawValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a n : M.Value) : ℕ → M.Value
  | 0 => F.graphValue (realMatrixDomainValue n n) (M.standard .real) matrixIdentityBody
  | k + 1 => F.graphValue (realMatrixDomainValue n n) (M.standard .complex)
      (matrixMultiplyRawBody (matrixPowerRawValue a n k) a n)

noncomputable def matrixPowerValue {M : Semantics.{u}} [FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β) : ℕ → M.Value :=
  matrixPowerRawValue a (denote n)

theorem matrixPowerValue_inFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β) (k : ℕ) :
    M.mem (matrixPowerValue a n k) (F.fnSetValue (matrixDomain n n) (M.standard .complex)) := by
  cases k with
  | zero =>
    exact F.fnSet_of_returns
      (F.graph_inFnSet _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _))
      (fun q hq => M.real_subset_complex _ (F.call_mem _ _ _ _
        (F.graph_inFnSet _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _)) hq))
  | succ k => exact F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩)

theorem matrixPowerValue_inRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β)
    (hn : In n N)
    (ha : M.mem a (F.fnSetValue (matrixDomain n n) (M.standard .real))) (k : ℕ) :
    M.mem (matrixPowerValue a n k) (F.fnSetValue (matrixDomain n n) (M.standard .real)) := by
  induction k with
  | zero => exact F.graph_inFnSet _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _)
  | succ k ih =>
    let prev := semanticObject (matrixPowerValue a n k) (M.member_isSet ih)
    let input := semanticObject a (M.member_isSet ha)
    have hprev : In prev (fnSet (matrixEntrywiseSignature n n .real)) := ih
    have hinput : In input (fnSet (matrixEntrywiseSignature n n .real)) := ha
    exact matrixMultiplyInRealFnSet
      (matrixMultiply prev input n n n hn hn hn
        (functionRealToComplex hprev) (functionRealToComplex hinput)) hprev hinput

structure MatrixPowerObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β
  exponent : Obj (M := M) γ

noncomputable instance matrixPowerRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixPowerObj (M := M) α β γ) where
  wd p := In p.order N ∧ In p.exponent N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := matrixPowerValue (denote p.matrix) p.order (NativeBridge.naturalValue (denote p.exponent))
  wd_isSet _ := M.member_isSet (matrixPowerValue_inFnSet _ _ _)

noncomputable def matrixPower {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (k : Obj (M := M) γ)
    (hn : In n N) (hk : In k N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixPowerObj (M := M) α β γ) := ⟨⟨a,n,k⟩,hn,hk,ha⟩

theorem matrixPowerInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixPowerObj (M := M) α β γ)) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .complex)) :=
  matrixPowerValue_inFnSet _ _ _

theorem matrixPowerInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixPowerObj (M := M) α β γ))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .real)) :=
  matrixPowerValue_inRealFnSet _ _ p.wd.1 ha _

theorem matrixPowerZero {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) :
    matrixPowerValue (denote a) n (NativeBridge.naturalValue (M.number 0)) =
      F.graphValue (matrixDomain n n) (M.standard .real) matrixIdentityBody := by
  have h := NativeBridge.naturalValue_number (M := M) 0
  simp only [Nat.cast_zero] at h
  rw [h]
  rfl

theorem matrixPowerSuccessor {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (k : Obj (M := M) γ) (hk : In k N) :
    matrixPowerValue (denote a) n (NativeBridge.naturalValue (M.addValue (denote k) (M.number 1))) =
      F.graphValue (matrixDomain n n) (M.standard .complex)
        (matrixMultiplyBody (matrixPowerValue (denote a) n (NativeBridge.naturalValue (denote k))) (denote a) n) := by
  have h : NativeBridge.naturalValue (M.addValue (denote k) (M.number 1)) =
      NativeBridge.naturalValue (denote k) + 1 := by
    conv_lhs => rw [NativeBridge.naturalValue_spec (denote k) hk, M.add_numbers]
    have hn := NativeBridge.naturalValue_number (M := M) (NativeBridge.naturalValue (denote k) + 1)
    simpa only [Nat.cast_add, Nat.cast_one] using hn
  rw [h]
  rfl
end Litex

namespace Litex
theorem matrixMinorIndexFloor (n r k : ℤ) (hn : 0 < n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hk : 1 ≤ k) (hkn : k < n) :
    (k : ℝ) + (⌊((k : ℝ) + n - r) / n⌋ : ℤ) =
      ((if k < r then k else k + 1 : ℤ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrnR : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  by_cases hkr : k < r
  · have hkrR : (k : ℝ) < r := by exact_mod_cast hkr
    have hf : ⌊((k : ℝ) + n - r) / n⌋ = (0 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num only [Int.cast_zero]
        apply div_nonneg _ (le_of_lt hnR)
        linarith
      · rw [div_lt_iff₀ hnR]
        norm_num
        linarith
    simp only [if_pos hkr, hf, Int.cast_zero, add_zero]
  · have hkrR : (r : ℝ) ≤ k := by exact_mod_cast (le_of_not_gt hkr)
    have hf : ⌊((k : ℝ) + n - r) / n⌋ = (1 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · rw [le_div_iff₀ hnR]
        norm_num
        linarith
      · rw [div_lt_iff₀ hnR]
        norm_num
        linarith
    simp only [if_neg hkr, hf, Int.cast_add, Int.cast_one]
theorem matrixMinorIndexBounds (n r k : ℤ) (hk : 1 ≤ k) (hkn : k < n) :
    let shifted := if k < r then k else k + 1
    1 ≤ shifted ∧ shifted ≤ n ∧ shifted ≠ r := by
  dsimp only
  split_ifs <;> omega
end Litex

namespace Litex
theorem closedRangeValue_members {M : Semantics.{u}} [S : SetSemantics M]
    (lower upper : ℤ) (x : M.Value) :
    M.mem x (closedRangeValue (M.number (lower : ℂ)) (M.number (upper : ℂ))) ↔
      ∃ k : ℤ, x = M.number (k : ℂ) ∧ lower ≤ k ∧ k ≤ upper := by
  rw [closedRangeValue, S.sep_members]
  constructor
  · rintro ⟨_, l, u, k, hl, hu, hx, hlo, hhi⟩
    have hle : lower = l := by exact_mod_cast M.number_injective hl
    have hue : upper = u := by exact_mod_cast M.number_injective hu
    subst l u
    exact ⟨k,hx,hlo,hhi⟩
  · rintro ⟨k,hx,hlo,hhi⟩
    exact ⟨(M.integer_members _).mpr ⟨k,hx⟩,lower,upper,k,rfl,rfl,hx,hlo,hhi⟩

theorem closedRangeValueListMembers {M : Semantics.{u}} [SetSemantics M]
    (a b : ℤ) (xs : List ℤ) (hs : Finset.Icc a b = xs.toFinset) (x : M.Value) :
    M.mem x (closedRangeValue (M.number (a : ℂ)) (M.number (b : ℂ))) ↔
      x ∈ xs.map (fun (k : ℤ) => M.number (k : ℂ)) := by
  rw [closedRangeValue_members]
  constructor
  · rintro ⟨k, hx, hlo, hhi⟩
    apply List.mem_map.mpr
    exact ⟨k, List.mem_toFinset.mp (hs ▸ Finset.mem_Icc.mpr ⟨hlo,hhi⟩), hx.symm⟩
  · intro hx
    obtain ⟨k, hk, hx⟩ := List.mem_map.mp hx
    have bounds := Finset.mem_Icc.mp (hs.symm ▸ List.mem_toFinset.mpr hk)
    exact ⟨k, hx.symm, bounds.1, bounds.2⟩

noncomputable def matrixMinorShift {M : Semantics.{u}} (n deleted k : M.Value) : M.Value :=
  M.addValue k (roundingValue false (M.divValue (M.subValue (M.addValue k n) deleted) n))

theorem matrixMinorShift_numbers {M : Semantics.{u}} (n r k : ℤ) (hn : 0 < n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hk : 1 ≤ k) (hkn : k < n) :
    matrixMinorShift (M.number (n : ℂ)) (M.number (r : ℂ)) (M.number (k : ℂ)) =
      M.number ((if k < r then k else k + 1 : ℤ) : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  unfold matrixMinorShift
  rw [M.add_numbers, M.sub_numbers, M.div_numbers _ _ hnC]
  have hrnd := roundingValue_number (M := M) false (((k : ℝ) + n - r) / n)
  simp only [Bool.false_eq_true, ↓reduceIte, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_intCast] at hrnd
  rw [hrnd, M.add_numbers]
  apply congrArg M.number
  have h := congrArg (fun z : ℝ => (z : ℂ)) (matrixMinorIndexFloor n r k hn hr hrn hk hkn)
  simpa only [Complex.ofReal_add, Complex.ofReal_intCast] using h

noncomputable def matrixMinorIndexValue {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) : M.Value :=
  closedRangeValue (M.number 1) (M.subValue (denote n) (M.number 1))

theorem matrixMinorShift_mem {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n NPos)
    (r k : M.Value) (hr : M.mem r (matrixIndexValue n))
    (hk : M.mem k (matrixMinorIndexValue n)) :
    M.mem (matrixMinorShift (denote n) r k) (matrixIndexValue n) := by
  obtain ⟨nz, hnz, hnpos⟩ := integerWitnessOfNPos n hn
  change M.mem r (closedRangeValue (M.number 1) (denote n)) at hr
  change M.mem k (closedRangeValue (M.number 1) (M.subValue (denote n) (M.number 1))) at hk
  change M.mem _ (closedRangeValue (M.number 1) (denote n))
  rw [hnz] at hr hk ⊢
  rw [M.sub_numbers] at hk
  have hR := closedRangeValue_members (M := M) 1 nz r
  have hK := closedRangeValue_members (M := M) 1 (nz - 1) k
  simp only [Int.cast_one] at hR
  simp only [Int.cast_sub, Int.cast_one] at hK
  obtain ⟨rz,hrz,hrlo,hrhi⟩ := hR.mp hr
  obtain ⟨kz,hkz,hklo,hkhi⟩ := hK.mp hk
  rw [hrz, hkz, matrixMinorShift_numbers nz rz kz hnpos hrlo hrhi hklo (by omega)]
  have hOut := closedRangeValue_members (M := M) 1 nz (M.number ((if kz < rz then kz else kz+1 : ℤ) : ℂ))
  simp only [Int.cast_one] at hOut
  have bounds := matrixMinorIndexBounds nz rz kz hklo (by omega)
  exact hOut.mpr ⟨_,rfl,bounds.1,bounds.2.1⟩
end Litex

namespace Litex
noncomputable def matrixMinorDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) : M.Value :=
  F.sepValue (FiniteFunction.cartValue ![matrixMinorIndexValue n, matrixMinorIndexValue n]) (fun _ => True)

theorem matrixMinorDomain_isSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) : M.isSet (matrixMinorDomain n) :=
  F.sep_isSet _ _ (FiniteFunction.cart_isSet _ (by
    intro i; fin_cases i <;> exact F.sep_isSet _ _ (M.standard_isSet .integer)))

noncomputable def matrixMinorSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (scalar : StandardSetValue) : FunctionSignature M :=
  ⟨matrixMinorDomain n, matrixMinorDomain_isSet n, M.standard scalar, M.standard_isSet scalar⟩

noncomputable def matrixMinorBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (a n r c q : M.Value) : M.Value :=
  F.callValue a (FiniteFunction.pack2
    (matrixMinorShift n r (FiniteFunction.unpack2 q).1)
    (matrixMinorShift n c (FiniteFunction.unpack2 q).2))

theorem matrixMinorBody_mem {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n NPos)
    (a r c : M.Value) (hr : M.mem r (matrixIndexValue n)) (hc : M.mem c (matrixIndexValue n))
    (scalar : StandardSetValue) (ha : M.mem a (F.fnSetValue (matrixDomain n n) (M.standard scalar)))
    (q : M.Value) (hq : M.mem q (matrixMinorDomain n)) :
    M.mem (matrixMinorBody a (denote n) r c q) (M.standard scalar) := by
  obtain ⟨x,hx,y,hy,rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp ((F.sep_members _ _ _).mp hq).1
  unfold matrixMinorBody
  rw [FiniteFunction.unpack_pack2]
  exact F.call_mem _ _ _ _ ha (matrixDomain_pair n n _ _
    (matrixMinorShift_mem n hn r x hr hx) (matrixMinorShift_mem n hn c y hc hy))

structure MatrixMinorObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x) (δ : Type t)
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β
  row : Obj (M := M) γ
  col : Obj (M := M) δ

noncomputable instance matrixMinorRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixMinorObj (M := M) α β γ δ) where
  wd p := In p.order NPos ∧ M.mem (denote p.row) (matrixIndexValue p.order) ∧
    M.mem (denote p.col) (matrixIndexValue p.order) ∧ In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := F.graphValue (matrixMinorDomain p.order) (M.standard .complex)
    (matrixMinorBody (denote p.matrix) (denote p.order) (denote p.row) (denote p.col))
  wd_isSet {p} h := M.member_isSet (F.graph_inFnSet _ _ _
    (matrixMinorBody_mem p.order h.1 _ _ _ h.2.1 h.2.2.1 .complex h.2.2.2.2))

noncomputable def matrixMinor {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (r : Obj (M := M) γ) (c : Obj (M := M) δ)
    (hp : In n NPos) (hr : M.mem (denote r) (matrixIndexValue n)) (hc : M.mem (denote c) (matrixIndexValue n))
    (hn : In n N) (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixMinorObj (M := M) α β γ δ) := ⟨⟨a,n,r,c⟩,hp,hr,hc,hn,ha⟩

theorem matrixMinorInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ)) :
    In p (fnSet (matrixMinorSignature p.val.order .complex)) :=
  F.graph_inFnSet _ _ _ (matrixMinorBody_mem p.val.order p.wd.1 _ _ _ p.wd.2.1 p.wd.2.2.1 .complex p.wd.2.2.2.2)

theorem matrixMinorCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ)) (q : M.Value) (hq : M.mem q (matrixMinorDomain p.val.order)) :
    F.callValue (denote p) q = matrixMinorBody (denote p.val.matrix) (denote p.val.order) (denote p.val.row) (denote p.val.col) q :=
  F.call_graphValue _ _ _ (matrixMinorBody_mem p.val.order p.wd.1 _ _ _ p.wd.2.1 p.wd.2.2.1 .complex p.wd.2.2.2.2) q hq

theorem matrixMinorInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) :
    In p (fnSet (matrixMinorSignature p.val.order .real)) := by
  apply F.fnSet_of_returns (matrixMinorInFnSet p)
  intro q hq
  rw [matrixMinorCall p q hq]
  exact matrixMinorBody_mem p.val.order p.wd.1 _ _ _ p.wd.2.1 p.wd.2.2.1 .real ha q hq

theorem matrixMinor_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixMinorDomain p.val.order)
    (hb : g.val.bodyValue = matrixMinorBody (denote p.val.matrix) (denote p.val.order) (denote p.val.row) (denote p.val.col)) : Same p g := by
  apply functionExtOnDomain p g (matrixMinorSignature p.val.order .complex) g.val.signature
    (matrixMinorInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixMinorCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hb q)).symm
end Litex

namespace Litex

theorem matrixPredecessorNatural {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n NPos) :
    M.mem (M.subValue (denote n) (M.number 1)) (M.standard .natural) := by
  obtain ⟨z,hz,hpos⟩ := integerWitnessOfNPos n hn
  rw [hz, M.sub_numbers]
  apply (M.natural_members _).mpr
  refine ⟨(z-1).toNat, congrArg M.number ?_⟩
  have h : ((z-1).toNat : ℤ) = z-1 := Int.toNat_of_nonneg (by omega)
  exact_mod_cast h.symm

noncomputable def matrixCofactorRawValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a n r c : M.Value) : M.Value :=
  let indices := closedRangeValue (M.number 1) (M.subValue n (M.number 1))
  let domain := F.sepValue (FiniteFunction.cartValue ![indices, indices]) (fun _ => True)
  let minor := F.graphValue domain (M.standard .complex) (matrixMinorBody a n r c)
  let size := NativeBridge.naturalValue (M.subValue n (M.number 1))
  M.number ((-1 : ℂ) ^ NativeBridge.naturalValue (M.addValue r c) * (matrixComplexOn minor size size).det)


noncomputable def matrixCofactorValue {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α) (r c : M.Value) : M.Value :=
  matrixCofactorRawValue a (denote n) r c

structure MatrixCofactorObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x) (δ : Type t)
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    extends MatrixMinorObj (M := M) α β γ δ

noncomputable instance matrixCofactorRepresentation {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixCofactorObj (M := M) α β γ δ) where
  wd p := WD (M := M) p.toMatrixMinorObj
  denote p := matrixCofactorValue (denote p.matrix) p.order (denote p.row) (denote p.col)
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_,rfl⟩)

noncomputable def matrixCofactor {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (r : Obj (M := M) γ) (c : Obj (M := M) δ)
    (hp : In n NPos) (hr : M.mem (denote r) (matrixIndexValue n)) (hc : M.mem (denote c) (matrixIndexValue n))
    (hn : In n N) (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixCofactorObj (M := M) α β γ δ) := ⟨⟨⟨a,n,r,c⟩⟩,hp,hr,hc,hn,ha⟩

theorem matrixCofactorInC {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixCofactorObj (M := M) α β γ δ)) : In p C :=
  (M.complex_members _).mpr ⟨_,rfl⟩

theorem matrixCofactorInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixCofactorObj (M := M) α β γ δ))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) : In p R := by
  let minor : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ) := ⟨p.val.toMatrixMinorObj,p.wd⟩
  have hn := matrixPredecessorNatural p.val.order p.wd.1
  let dim := semanticObject (M.subValue (denote p.val.order) (M.number 1)) (M.member_isSet hn)
  let det := matrixDeterminant minor dim hn (matrixMinorInFnSet minor)
  obtain ⟨value,hvalue⟩ := (M.real_members _).mp (matrixDeterminantInR det (matrixMinorInRealFnSet minor ha))
  have hdet : (matrixComplexOn (denote minor) (NativeBridge.naturalValue (denote dim)) (NativeBridge.naturalValue (denote dim))).det = (value : ℂ) := M.number_injective hvalue
  apply (M.real_members _).mpr
  refine ⟨(-1 : ℝ) ^ NativeBridge.naturalValue (M.addValue (denote p.val.row) (denote p.val.col)) * value, ?_⟩
  have h := congrArg (fun z : ℂ => M.number ((-1 : ℂ) ^ NativeBridge.naturalValue (M.addValue (denote p.val.row) (denote p.val.col)) * z)) hdet
  exact h.trans (by congr 1; push_cast; rfl)

theorem matrixCofactorOne {M : Semantics.{u}} [FunctionSemantics M] (a : M.Value) :
    matrixCofactorValue a (number 1) (M.number 1) (M.number 1) = M.number 1 := by
  unfold matrixCofactorValue matrixCofactorRawValue
  change M.number ((-1 : ℂ) ^ NativeBridge.naturalValue (M.addValue (M.number 1) (M.number 1)) *
    (matrixComplexOn _ (NativeBridge.naturalValue (M.subValue (M.number 1) (M.number 1))) _).det) = _
  rw [M.add_numbers, M.sub_numbers]
  simp only [one_add_one_eq_two]
  have h0 : NativeBridge.naturalValue (M.number ((1 : ℂ) - 1)) = 0 := by
    simpa only [sub_self, Nat.cast_zero] using (NativeBridge.naturalValue_number (M := M) 0)
  have h2 := NativeBridge.naturalValue_number (M := M) 2
  norm_num only [Nat.cast_ofNat] at h2
  rw [h0,h2,Matrix.det_fin_zero]
  norm_num

theorem matrixEntryValue_spec {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (n r c : ℕ)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number (n : ℂ)) (number (n : ℂ))) (M.standard .complex)))
    (hr : 1 ≤ r) (hrn : r ≤ n) (hc : 1 ≤ c) (hcn : c ≤ n) :
    matrixEntryValue a r c = M.number (NativeBridge.complexValue (matrixEntryValue a r c)) :=
  NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha
    (matrixDomain_pair _ _ _ _ (matrixIndexNaturalNumber n r hr hrn) (matrixIndexNaturalNumber n c hc hcn)))

theorem matrixCofactorTwo {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (r c : ℕ) (hr : r=1 ∨ r=2) (hc : c=1 ∨ c=2)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number (r : ℂ)) (M.number (c : ℂ)) =
      M.number ((-1 : ℂ) ^ (r+c) * NativeBridge.complexValue (matrixEntryValue a (3-r) (3-c))) := by
  have hsize : NativeBridge.naturalValue (M.subValue (M.number 2) (M.number 1)) = 1 := by
    rw [M.sub_numbers]
    rw [show (2 : ℂ) - 1 = 1 by norm_num]
    simpa only [Nat.cast_one] using (NativeBridge.naturalValue_number (M := M) 1)
  have hsum : NativeBridge.naturalValue (M.addValue (M.number (r : ℂ)) (M.number (c : ℂ))) = r+c := by
    rw [M.add_numbers, ← Nat.cast_add, NativeBridge.naturalValue_number]
  unfold matrixCofactorValue matrixCofactorRawValue
  change M.number ((-1 : ℂ) ^ NativeBridge.naturalValue (M.addValue (M.number (r : ℂ)) (M.number (c : ℂ))) *
    (matrixComplexOn _ (NativeBridge.naturalValue (M.subValue (M.number 2) (M.number 1))) _).det) = _
  rw [hsum,hsize,Matrix.det_fin_one]
  simp only [matrixComplexOn, FiniteFunction.index, Fin.val_zero, zero_add, Nat.cast_one]
  apply congrArg M.number
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ (r+c) * z)
  apply congrArg (NativeBridge.complexValue (M := M))
  have hp := numberInNPosOfEq (M := M) 2 2 (by norm_num) (by omega)
  have hri : M.mem (M.number (r : ℂ)) (matrixIndexValue (number 2)) := by
    simpa only [Nat.cast_ofNat] using (matrixIndexNaturalNumber (M := M) 2 r (by omega) (by omega))
  have hci : M.mem (M.number (c : ℂ)) (matrixIndexValue (number 2)) := by
    simpa only [Nat.cast_ofNat] using (matrixIndexNaturalNumber (M := M) 2 c (by omega) (by omega))
  have hdim : matrixMinorIndexValue (number (M := M) 2) = matrixIndexValue (number 1) := by
    change closedRangeValue (M.number 1) (M.subValue (M.number 2) (M.number 1)) = closedRangeValue (M.number 1) (M.number 1)
    rw [M.sub_numbers]
    norm_num
  have hi : M.mem (M.number 1) (matrixIndexValue (number 1)) := by
    simpa only [Nat.cast_one] using (matrixIndexNaturalNumber (M := M) 1 1 (by omega) (by omega))
  have hq : M.mem (FiniteFunction.pack2 (M.number 1) (M.number 1)) (matrixMinorDomain (number 2)) := by
    unfold matrixMinorDomain
    rw [hdim]
    exact matrixDomain_pair _ _ _ _ hi hi
  change F.callValue (F.graphValue (matrixMinorDomain (number 2)) (M.standard .complex)
    (matrixMinorBody a (denote (number 2)) (M.number (r : ℂ)) (M.number (c : ℂ))))
    (FiniteFunction.pack2 (M.number 1) (M.number 1)) = matrixEntryValue a (3-r) (3-c)
  rw [F.call_graphValue _ _ _ (matrixMinorBody_mem (number 2) hp a _ _ hri hci .complex ha) _ hq]
  unfold matrixMinorBody
  rw [FiniteFunction.unpack_pack2]
  have hs : ∀ k : ℕ, k=1 ∨ k=2 →
      matrixMinorShift (M.number 2) (M.number (k : ℂ)) (M.number 1) = M.number ((3-k : ℕ) : ℂ) := by
    intro k hk
    rcases hk with rfl | rfl
    · have h := matrixMinorShift_numbers (M := M) 2 1 1 (by omega) (by omega) (by omega) (by omega) (by omega)
      norm_num at h ⊢
      exact h
    · have h := matrixMinorShift_numbers (M := M) 2 2 1 (by omega) (by omega) (by omega) (by omega) (by omega)
      norm_num at h ⊢
      exact h
  change F.callValue a (FiniteFunction.pack2 (matrixMinorShift (M.number 2) (M.number (r : ℂ)) (M.number 1)) (matrixMinorShift (M.number 2) (M.number (c : ℂ)) (M.number 1))) = _
  rw [hs r hr,hs c hc]
  rfl

theorem matrixCofactorTwo11 {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number 1) (M.number 1) = matrixEntryValue a 2 2 := by
  have h := matrixCofactorTwo a 1 1 (by decide) (by decide) ha
  have he := matrixEntryValue_spec a 2 2 2 ha (by omega) (by omega) (by omega) (by omega)
  norm_num at h
  exact h.trans he.symm

theorem matrixCofactorTwo12 {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number 1) (M.number 2) = M.negValue (matrixEntryValue a 2 1) := by
  have h := matrixCofactorTwo a 1 2 (by decide) (by decide) ha
  have he := matrixEntryValue_spec a 2 2 1 ha (by omega) (by omega) (by omega) (by omega)
  norm_num at h
  exact h.trans ((congrArg M.negValue he).trans (M.neg_numbers _)).symm

theorem matrixCofactorTwo21 {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number 2) (M.number 1) = M.negValue (matrixEntryValue a 1 2) := by
  have h := matrixCofactorTwo a 2 1 (by decide) (by decide) ha
  have he := matrixEntryValue_spec a 2 1 2 ha (by omega) (by omega) (by omega) (by omega)
  norm_num at h
  exact h.trans ((congrArg M.negValue he).trans (M.neg_numbers _)).symm

theorem matrixCofactorTwo22 {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number 2) (M.number 2) = matrixEntryValue a 1 1 := by
  have h := matrixCofactorTwo a 2 2 (by decide) (by decide) ha
  have he := matrixEntryValue_spec a 2 1 1 ha (by omega) (by omega) (by omega) (by omega)
  norm_num at h
  exact h.trans he.symm
end Litex

namespace Litex
theorem matrixIndexPositiveOrder {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α)
    (r : M.Value) (hr : M.mem r (matrixIndexValue n)) : In n NPos := by
  obtain ⟨_, lower, upper, k, hl, hu, _, hlo, hhi⟩ := (F.sep_members _ _ _).mp hr
  change M.number 1 = M.number (lower : ℂ) at hl
  have hlower : lower = 1 := by
    have h := M.number_injective hl
    exact_mod_cast h.symm
  exact integerPositiveOfWitness n upper hu (by omega)

noncomputable def matrixAdjugateBody {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α)
    (q : M.Value) : M.Value :=
  matrixCofactorValue a n (FiniteFunction.unpack2 q).2 (FiniteFunction.unpack2 q).1

structure MatrixAdjugateObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β

noncomputable instance matrixAdjugateRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixAdjugateObj (M := M) α β) where
  wd p := In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := F.graphValue (matrixDomain p.order p.order) (M.standard .complex)
    (matrixAdjugateBody (denote p.matrix) p.order)
  wd_isSet {_} _ := M.member_isSet (F.graph_inFnSet _ _ _
    (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩))

noncomputable def matrixAdjugate {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixAdjugateObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha⟩

theorem matrixAdjugateInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixAdjugateObj (M := M) α β)) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .complex)) :=
  F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩)

theorem matrixAdjugateCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixAdjugateObj (M := M) α β)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.order p.val.order)) :
    F.callValue (denote p) q = matrixAdjugateBody (denote p.val.matrix) p.val.order q :=
  F.call_graphValue _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩) q hq

theorem matrixAdjugateInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixAdjugateObj (M := M) α β))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .real)) := by
  apply F.fnSet_of_returns (matrixAdjugateInFnSet p)
  intro q hq
  rw [matrixAdjugateCall p q hq]
  have hr := ((F.sep_members _ _ _).mp (matrixDomain_first p.val.order p.val.order q hq)).1
  have hc := ((F.sep_members _ _ _).mp (matrixDomain_second p.val.order p.val.order q hq)).1
  let r := semanticObject (FiniteFunction.unpack2 q).1 (M.member_isSet hr)
  let c := semanticObject (FiniteFunction.unpack2 q).2 (M.member_isSet hc)
  let cofactor := matrixCofactor p.val.matrix p.val.order c r
    (matrixIndexPositiveOrder p.val.order _ hr) hc hr p.wd.1 p.wd.2
  exact matrixCofactorInR cofactor ha

theorem matrixAdjugate_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixAdjugateObj (M := M) α β)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.order p.val.order)
    (hb : g.val.bodyValue = matrixAdjugateBody (denote p.val.matrix) p.val.order) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.order p.val.order .complex) g.val.signature
    (matrixAdjugateInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixAdjugateCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hb q)).symm
end Litex

namespace Litex

noncomputable def matrixInverseBody {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α)
    (q : M.Value) : M.Value :=
  M.divValue (matrixAdjugateBody a n q) (matrixDeterminantValue a n)

theorem matrixInverseBody_closed {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α)
    (hd : matrixDeterminantValue a n ≠ M.number 0) (q : M.Value) :
    M.mem (matrixInverseBody a n q) (M.standard .complex) :=
  M.div_closed ((M.complex_members _).mpr ⟨_,rfl⟩)
    ((M.complex_members _).mpr ⟨_,rfl⟩) hd

structure MatrixInverseObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β

noncomputable instance matrixInverseRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixInverseObj (M := M) α β) where
  wd p := In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex)) ∧
    matrixDeterminantValue (denote p.matrix) p.order ≠ M.number 0
  denote p := F.graphValue (matrixDomain p.order p.order) (M.standard .complex)
    (matrixInverseBody (denote p.matrix) p.order)
  wd_isSet {p} h := M.member_isSet (F.graph_inFnSet _ _ _
    (fun q _ => matrixInverseBody_closed _ p.order h.2.2 q))

noncomputable def matrixInverse {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hd : matrixDeterminantValue (denote a) n ≠ M.number 0) :
    Obj (M := M) (MatrixInverseObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha,hd⟩

theorem matrixInverseInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixInverseObj (M := M) α β)) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .complex)) :=
  F.graph_inFnSet _ _ _ (fun q _ => matrixInverseBody_closed _ p.val.order p.wd.2.2 q)

theorem matrixInverseCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixInverseObj (M := M) α β)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.order p.val.order)) :
    F.callValue (denote p) q = matrixInverseBody (denote p.val.matrix) p.val.order q :=
  F.call_graphValue _ _ _ (fun q _ => matrixInverseBody_closed _ p.val.order p.wd.2.2 q) q hq

theorem matrixInverseInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixInverseObj (M := M) α β))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .real)) := by
  apply F.fnSet_of_returns (matrixInverseInFnSet p)
  intro q hq
  rw [matrixInverseCall p q hq]
  let adj := matrixAdjugate p.val.matrix p.val.order p.wd.1 p.wd.2.1
  have haR := F.call_mem _ _ _ q (matrixAdjugateInRealFnSet adj ha) hq
  rw [matrixAdjugateCall adj q hq] at haR
  let det := matrixDeterminant p.val.matrix p.val.order p.wd.1 p.wd.2.1
  let numerator := semanticObject (matrixAdjugateBody (denote p.val.matrix) p.val.order q) (M.member_isSet haR)
  exact divInR numerator det haR (matrixDeterminantInR det ha) p.wd.2.2

theorem matrixInverse_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixInverseObj (M := M) α β)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.order p.val.order)
    (hb : g.val.bodyValue = matrixInverseBody (denote p.val.matrix) p.val.order) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.order p.val.order .complex) g.val.signature
    (matrixInverseInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixInverseCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hb q)).symm
end Litex

namespace Litex

noncomputable def matrixRankValue {M : Semantics.{u}} [FunctionSemantics M]
    (a m n : M.Value) : M.Value :=
  M.number ((matrixComplexOn a (NativeBridge.naturalValue m)
    (NativeBridge.naturalValue n)).rank : ℂ)

structure MatrixRankObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ

noncomputable instance matrixRankRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixRankObj (M := M) α β γ) where
  wd p := In p.rows N ∧ In p.cols N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.rows p.cols) (M.standard .complex))
  denote p := matrixRankValue (denote p.matrix) (denote p.rows) (denote p.cols)
  wd_isSet _ := M.member_isSet ((M.natural_members _).mpr ⟨_,rfl⟩)

noncomputable def matrixRank {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixRankObj (M := M) α β γ) := ⟨⟨a,m,n⟩,hm,hn,ha⟩

theorem matrixRankInN {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixRankObj (M := M) α β γ)) : In p N :=
  (M.natural_members _).mpr ⟨_,rfl⟩

theorem matrixRankLeRows {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixRankObj (M := M) α β γ)) : Le p p.val.rows := by
  let a := matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols
  refine NativeBridge.leOfDenoteReal p p.val.rows (a.rank : ℝ)
    (NativeBridge.naturalValue (denote p.val.rows) : ℝ) ?_ ?_ ?_
  · change M.number (a.rank : ℂ) = _
    simp only [Complex.ofReal_natCast]
  · simpa only [Complex.ofReal_natCast] using NativeBridge.naturalValue_spec (denote p.val.rows) p.wd.1
  · exact_mod_cast Matrix.rank_le_height a

theorem matrixRankLeCols {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixRankObj (M := M) α β γ)) : Le p p.val.cols := by
  let a := matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols
  refine NativeBridge.leOfDenoteReal p p.val.cols (a.rank : ℝ)
    (NativeBridge.naturalValue (denote p.val.cols) : ℝ) ?_ ?_ ?_
  · change M.number (a.rank : ℂ) = _
    simp only [Complex.ofReal_natCast]
  · simpa only [Complex.ofReal_natCast] using NativeBridge.naturalValue_spec (denote p.val.cols) p.wd.2.1
  · exact_mod_cast Matrix.rank_le_width a

theorem matrixComplexValue_zero {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (hm : In m N) (hn : In n N) :
    matrixComplexValue (denote (zeroMatrix m n hm hn)) m n = 0 := by
  ext i j
  unfold matrixComplexValue matrixComplexOn
  rw [zeroMatrixCall _ _ (matrixDomain_pair _ _ _ _ (matrixIndexOfFin m hm i) (matrixIndexOfFin n hn j))]
  exact NativeBridge.complexValue_number 0

theorem matrixRankZero {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (hm : In m N) (hn : In n N) :
    matrixRankValue (denote (zeroMatrix m n hm hn)) (denote m) (denote n) = M.number 0 := by
  change M.number ((matrixComplexValue (denote (zeroMatrix m n hm hn)) m n).rank : ℂ) = M.number 0
  rw [matrixComplexValue_zero m n hm hn, Matrix.rank_zero]
  simp only [Nat.cast_zero]

theorem matrixRankIdentity {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α]
    (n : Obj (M := M) α) (hn : In n N) :
    matrixRankValue (denote (identityMatrix n hn)) (denote n) (denote n) = denote n := by
  change M.number ((matrixComplexValue (denote (identityMatrix n hn)) n n).rank : ℂ) = denote n
  rw [matrixComplexValue_identity n hn, Matrix.rank_one, Fintype.card_fin]
  exact (NativeBridge.naturalValue_spec (denote n) hn).symm

theorem matrixRankTranspose {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ)) :
    matrixRankValue (denote p) (denote p.val.cols) (denote p.val.rows) =
      matrixRankValue (denote p.val.matrix) (denote p.val.rows) (denote p.val.cols) := by
  change M.number ((matrixComplexValue (denote p) p.val.cols p.val.rows).rank : ℂ) =
    M.number ((matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols).rank : ℂ)
  rw [matrixComplexValue_transpose, Matrix.rank_transpose]

open scoped ComplexOrder in
theorem matrixRankAdjoint {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ)) :
    matrixRankValue (denote p) (denote p.val.cols) (denote p.val.rows) =
      matrixRankValue (denote p.val.matrix) (denote p.val.rows) (denote p.val.cols) := by
  change M.number ((matrixComplexValue (denote p) p.val.cols p.val.rows).rank : ℂ) =
    M.number ((matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols).rank : ℂ)
  rw [matrixComplexValue_adjoint, Matrix.rank_conjTranspose]

end Litex



namespace Litex
theorem finiteAggregateOnPositive {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ))
    (hp : product = true)
    (hs : ∀ y, M.mem y p.val.signature.output → positiveRealPredicate y) :
    Lt (number 0) p := by
  classical
  apply (positiveRealPredicate_iff p).mp
  change positiveRealPredicate (M.number (finiteAggregateValue product _ _))
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf]
  apply positiveRealAggregate
  · intro i hi
    have ho := finiteAggregateOnCallInOutput p i (p.wd.1.mem_toFinset.mp hi)
    rw [← NativeBridge.complexValue_spec _ (p.wd.2.2.1 _ ho)]
    exact hs _ ho
  · exact Or.inl hp

end Litex
