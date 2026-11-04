import Litex.Multivariable
namespace Litex

theorem nativeRankSplitFactorizationExists {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ U : Matrix (Fin m) (Fin A.rank) ℂ,
    ∃ V : Matrix (Fin A.rank) (Fin n) ℂ,
    ∃ L : Matrix (Fin A.rank) (Fin m) ℂ,
    ∃ R : Matrix (Fin n) (Fin A.rank) ℂ,
      A = U*V ∧ L*U = 1 ∧ V*R = 1 := by
  classical
  let f := A.mulVecLin
  let S := LinearMap.range f
  let e : S ≃ₗ[ℂ] (Fin A.rank → ℂ) := (Module.finBasis ℂ S).equivFun
  obtain ⟨projection,hprojection⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  obtain ⟨section_,hsection⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let u := S.subtype.comp e.symm.toLinearMap
  let v := e.toLinearMap.comp f.rangeRestrict
  let l := e.toLinearMap.comp projection
  let r := section_.comp e.symm.toLinearMap
  have product : u.comp v = f := by
    apply LinearMap.ext
    intro x
    change S.subtype (e.symm (e (f.rangeRestrict x))) = f x
    rw [e.symm_apply_apply]
    rfl
  have left : l.comp u = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hprojection (e.symm x)
    change projection (S.subtype (e.symm x)) = e.symm x at h
    change e (projection (S.subtype (e.symm x))) = x
    rw [h,e.apply_symm_apply]
  have right : v.comp r = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hsection (e.symm x)
    change f.rangeRestrict (section_ (e.symm x)) = e.symm x at h
    change e (f.rangeRestrict (section_ (e.symm x))) = x
    rw [h,e.apply_symm_apply]
  refine ⟨LinearMap.toMatrix' u,LinearMap.toMatrix' v,
    LinearMap.toMatrix' l,LinearMap.toMatrix' r,?_,?_,?_⟩
  · rw [← LinearMap.toMatrix'_comp,product]
    exact (LinearMap.toMatrix'_toLin' A).symm
  · rw [← LinearMap.toMatrix'_comp,left,LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp,right,LinearMap.toMatrix'_id]

universe u v w x

noncomputable def nativeMatrixEntry {M : Semantics.{u}} [F : FunctionSemantics M]
    {rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) ℂ) (q : M.Value) : ℂ := by
  classical
  exact if h : ∃ p : Fin rows × Fin cols,
      q = FiniteFunction.pack2 (FiniteFunction.index p.1) (FiniteFunction.index p.2)
    then A (Classical.choose h).1 (Classical.choose h).2 else 0

theorem nativeMatrixEntryIndex {M : Semantics.{u}} [F : FunctionSemantics M]
    {rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) ℂ) (r : Fin rows) (c : Fin cols) :
    nativeMatrixEntry (M := M) A (FiniteFunction.pack2 (FiniteFunction.index r) (FiniteFunction.index c)) = A r c := by
  classical
  have h : ∃ p : Fin rows × Fin cols,
      FiniteFunction.pack2 (M := M) (FiniteFunction.index r) (FiniteFunction.index c) =
        FiniteFunction.pack2 (FiniteFunction.index p.1) (FiniteFunction.index p.2) := ⟨(r,c),rfl⟩
  unfold nativeMatrixEntry
  rw [dif_pos h]
  have indices := congrArg FiniteFunction.unpack2 (Classical.choose_spec h)
  rw [FiniteFunction.unpack_pack2,FiniteFunction.unpack_pack2] at indices
  have hr := FiniteFunction.index_injective (congrArg Prod.fst indices)
  have hc := FiniteFunction.index_injective (congrArg Prod.snd indices)
  rw [← hr,← hc]

noncomputable def nativeMatrixGraph {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β)
    (A : Matrix (Fin (NativeBridge.naturalValue (denote m)))
      (Fin (NativeBridge.naturalValue (denote n))) ℂ) : M.Value :=
  F.graphValue (matrixDomain m n) (M.standard .complex) (fun q => M.number (nativeMatrixEntry A q))

theorem nativeMatrixGraphInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β)
    (A : Matrix (Fin (NativeBridge.naturalValue (denote m)))
      (Fin (NativeBridge.naturalValue (denote n))) ℂ) :
    M.mem (nativeMatrixGraph m n A) (F.fnSetValue (matrixDomain m n) (M.standard .complex)) :=
  F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩)

noncomputable def matrixOfNative {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β)
    (A : Matrix (Fin (NativeBridge.naturalValue (denote m)))
      (Fin (NativeBridge.naturalValue (denote n))) ℂ) : Obj (M := M) M.Value :=
  semanticObject (nativeMatrixGraph m n A) (M.member_isSet (nativeMatrixGraphInFnSet m n A))

theorem matrixOfNativeInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β)
    (A : Matrix (Fin (NativeBridge.naturalValue (denote m)))
      (Fin (NativeBridge.naturalValue (denote n))) ℂ) :
    M.mem (denote (matrixOfNative m n A)) (F.fnSetValue (matrixDomain m n) (M.standard .complex)) :=
  nativeMatrixGraphInFnSet m n A

theorem matrixComplexValueOfNative {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (hm : In m N) (hn : In n N)
    (A : Matrix (Fin (NativeBridge.naturalValue (denote m)))
      (Fin (NativeBridge.naturalValue (denote n))) ℂ) :
    matrixComplexValue (denote (matrixOfNative m n A)) m n = A := by
  ext r c
  change NativeBridge.complexValue (F.callValue (nativeMatrixGraph m n A)
    (FiniteFunction.pack2 (FiniteFunction.index r) (FiniteFunction.index c))) = A r c
  unfold nativeMatrixGraph
  rw [F.call_graphValue _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩) _
    (matrixDomain_pair m n _ _ (matrixIndexOfFin m hm r) (matrixIndexOfFin n hn c)),
    NativeBridge.complexValue_number,nativeMatrixEntryIndex]

theorem matrixRankFactorizationExists {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (k : Obj (M := M) δ) (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (rank_value : denote k = matrixRankValue (denote a) (denote m) (denote n)) :
    ∃ U : Obj (M := M) M.Value,
    ∃ hU : M.mem (denote U) (F.fnSetValue (matrixDomain m k) (M.standard .complex)),
    ∃ V : Obj (M := M) M.Value,
    ∃ hV : M.mem (denote V) (F.fnSetValue (matrixDomain k n) (M.standard .complex)),
    ∃ L : Obj (M := M) M.Value,
    ∃ hL : M.mem (denote L) (F.fnSetValue (matrixDomain k m) (M.standard .complex)),
    ∃ R : Obj (M := M) M.Value,
    ∃ hR : M.mem (denote R) (F.fnSetValue (matrixDomain n k) (M.standard .complex)),
    ∃ hk : In k N,
      Same a (matrixMultiply U V m k n hm hk hn hU hV) ∧
      Same (matrixMultiply L U k m k hk hm hk hL hU) (identityMatrix k hk) ∧
      Same (matrixMultiply V R k n k hk hn hk hV hR) (identityMatrix k hk) := by
  classical
  have hk : In k N := (M.natural_members _).mpr ⟨_,rank_value⟩
  have size : NativeBridge.naturalValue (denote k) = (matrixComplexValue (denote a) m n).rank := by
    rw [rank_value]
    exact NativeBridge.naturalValue_number _
  have split : ∃ U : Matrix (Fin (NativeBridge.naturalValue (denote m))) (Fin (NativeBridge.naturalValue (denote k))) ℂ,
      ∃ V : Matrix (Fin (NativeBridge.naturalValue (denote k))) (Fin (NativeBridge.naturalValue (denote n))) ℂ,
      ∃ L : Matrix (Fin (NativeBridge.naturalValue (denote k))) (Fin (NativeBridge.naturalValue (denote m))) ℂ,
      ∃ R : Matrix (Fin (NativeBridge.naturalValue (denote n))) (Fin (NativeBridge.naturalValue (denote k))) ℂ,
        matrixComplexValue (denote a) m n = U*V ∧ L*U=1 ∧ V*R=1 := by
    rw [size]
    exact nativeRankSplitFactorizationExists _
  obtain ⟨U,V,L,R,product,left,right⟩ := split
  let u := matrixOfNative m k U
  let v := matrixOfNative k n V
  let l := matrixOfNative k m L
  let r := matrixOfNative n k R
  have hu := matrixOfNativeInFnSet m k U
  have hv := matrixOfNativeInFnSet k n V
  have hl := matrixOfNativeInFnSet k m L
  have hr := matrixOfNativeInFnSet n k R
  refine ⟨u,hu,v,hv,l,hl,r,hr,hk,?_,?_,?_⟩
  · apply matrixSameOfComplexMatrix a (matrixMultiply u v m k n hm hk hn hu hv) m n hm hn ha
      (matrixMultiplyInFnSet _)
    rw [matrixComplexValueMultiply,matrixComplexValueOfNative m k hm hk,
      matrixComplexValueOfNative k n hk hn]
    exact product
  · apply matrixSameOfComplexMatrix (matrixMultiply l u k m k hk hm hk hl hu)
      (identityMatrix k hk) k k hk hk (matrixMultiplyInFnSet _)
      (functionRealToComplex (identityMatrixInFnSet _))
    rw [matrixComplexValueMultiply,matrixComplexValue_identity,
      matrixComplexValueOfNative k m hk hm,matrixComplexValueOfNative m k hm hk]
    exact left
  · apply matrixSameOfComplexMatrix (matrixMultiply v r k n k hk hn hk hv hr)
      (identityMatrix k hk) k k hk hk (matrixMultiplyInFnSet _)
      (functionRealToComplex (identityMatrixInFnSet _))
    rw [matrixComplexValueMultiply,matrixComplexValue_identity,
      matrixComplexValueOfNative k n hk hn,matrixComplexValueOfNative n k hn hk]
    exact right

end Litex
