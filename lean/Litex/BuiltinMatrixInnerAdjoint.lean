import Litex.Multivariable
universe u v w x y z
namespace Litex

theorem finiteComplexAdjointInner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℂ) (a : κ → ℂ) (b : ι → ℂ) :
    (∑ i, star (∑ j, A i j * a j) * b i) =
      ∑ j, star (a j) * (∑ i, star (A i j) * b i) := by
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finiteInnerProductFiniteSum {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ)) :
    denote p = M.number (∑ i : Fin (NativeBridge.naturalValue (denote p.val.dimension)),
      star (NativeBridge.complexValue (F.callValue (denote p.val.left) (FiniteFunction.index i))) *
        NativeBridge.complexValue (F.callValue (denote p.val.right) (FiniteFunction.index i))) := by
  apply congrArg M.number
  change (finiteAggregateValue false (matrixIndexValue p.val.dimension)
    (fun k => NativeBridge.complexValue (finiteInnerProductTerm (denote p.val.left) (denote p.val.right) k))) = _
  rw [finiteSumMatrixIndex p.val.dimension p.wd.1]
  apply Finset.sum_congr rfl
  intro i _
  have member : M.mem (FiniteFunction.index (M := M) i) (finiteSeqDomain p.val.dimension) :=
    (F.sep_members _ _ _).mpr ⟨matrixIndexOfFin p.val.dimension p.wd.1 i,True.intro⟩
  obtain ⟨a,ha⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ p.wd.2.1 member)
  obtain ⟨b,hb⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ p.wd.2.2 member)
  unfold finiteInnerProductTerm
  rw [ha,hb,complexUnaryValue_number,M.mul_numbers,NativeBridge.complexValue_number,
    NativeBridge.complexValue_number,NativeBridge.complexValue_number]

theorem matrixApplyEntryFiniteSum {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ))
    (i : Fin (NativeBridge.naturalValue (denote p.val.rows))) :
    NativeBridge.complexValue (F.callValue (denote p) (FiniteFunction.index i)) =
      ∑ j : Fin (NativeBridge.naturalValue (denote p.val.cols)),
        matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols i j *
          NativeBridge.complexValue (F.callValue (denote p.val.vector) (FiniteFunction.index j)) := by
  rw [matrixApplyEntryComplex p _ (matrixIndexOfFin p.val.rows p.wd.1 i)]
  exact finiteSumMatrixIndex p.val.cols p.wd.2.1 _

theorem matrixInnerProductAdjoint {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y} {ε : Type z}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (A : Obj (M := M) α) (u : Obj (M := M) β) (v : Obj (M := M) γ)
    (m : Obj (M := M) δ) (n : Obj (M := M) ε) (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hu : M.mem (denote u) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hv : M.mem (denote v) (F.fnSetValue (finiteSeqDomain m) (M.standard .complex))) :
    Same
      (finiteInnerProduct (matrixApply A u m n hm hn hA hu) v m hm (matrixApplyInFnSet _) hv)
      (finiteInnerProduct u
        (matrixApply (conjugateTranspose A m n hm hn hA) v n m hn hm (conjugateTransposeInFnSet _) hv)
        n hn hu (matrixApplyInFnSet _)) := by
  let left := matrixApply A u m n hm hn hA hu
  let adjoint := conjugateTranspose A m n hm hn hA
  let right := matrixApply adjoint v n m hn hm (conjugateTransposeInFnSet adjoint) hv
  change denote (finiteInnerProduct left v m hm (matrixApplyInFnSet left) hv) =
    denote (finiteInnerProduct u right n hn hu (matrixApplyInFnSet right))
  rw [finiteInnerProductFiniteSum,finiteInnerProductFiniteSum]
  apply congrArg M.number
  let Af := matrixComplexValue (denote A) m n
  let uf := fun i : Fin (NativeBridge.naturalValue (denote n)) =>
    NativeBridge.complexValue (F.callValue (denote u) (FiniteFunction.index i))
  let vf := fun i : Fin (NativeBridge.naturalValue (denote m)) =>
    NativeBridge.complexValue (F.callValue (denote v) (FiniteFunction.index i))
  have leftEntries : ∀ i, NativeBridge.complexValue (F.callValue (denote left) (FiniteFunction.index i)) =
      ∑ j, Af i j * uf j := fun i => matrixApplyEntryFiniteSum left i
  have rightEntries : ∀ j, NativeBridge.complexValue (F.callValue (denote right) (FiniteFunction.index j)) =
      ∑ i, star (Af i j) * vf i := by
    intro j
    have entry : NativeBridge.complexValue (F.callValue (denote right) (FiniteFunction.index j)) =
        ∑ i, matrixComplexValue (denote adjoint) n m j i * vf i := matrixApplyEntryFiniteSum right j
    have hadj : matrixComplexValue (denote adjoint) n m = Af.conjTranspose := matrixComplexValue_adjoint adjoint
    exact entry.trans (Finset.sum_congr rfl (fun i _ =>
      congrArg (fun value : ℂ => value * vf i) (congrFun (congrFun hadj j) i)))
  calc
    _ = ∑ i, star (∑ j, Af i j * uf j) * vf i := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun value : ℂ => star value * vf i) (leftEntries i)
    _ = ∑ j, star (uf j) * (∑ i, star (Af i j) * vf i) := finiteComplexAdjointInner Af uf vf
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun value : ℂ => star (uf j) * value) (rightEntries j).symm

end Litex
