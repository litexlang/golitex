import Litex.FiniteSets

universe u v w
namespace Litex

theorem fnRangeFiniteOfFiniteCover {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (r : Obj (M := M) (FunctionRange (M := M) α)) (s : FunctionSignature M)
    (cover : Obj (M := M) β) (hf : In r.val.function (fnSet s))
    (finite : IsFiniteSet cover)
    (included : ∀ a, M.mem a s.domain → M.mem a (denote cover)) : IsFiniteSet r := by
  apply (finite.image (fun a => F.callValue (denote r.val.function) a)).subset
  intro y hy
  obtain ⟨a, ha, same⟩ := (F.range_mem_iff s.output_isSet hf).mp hy
  exact ⟨a, included a ha, same.symm⟩
end Litex
