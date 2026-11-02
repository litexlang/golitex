import Litex.ElementaryFunctions

universe u v w

namespace Litex

theorem seqSetSameOfCarrier {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (SeqSetObj (M := M) α))
    (t : Obj (M := M) (SeqSetObj (M := M) β))
    (hc : Same s.val.carrier t.val.carrier) : Same s t := by
  change F.fnSetValue (F.sepValue (denote (NPos (M := M))) (fun _ => True))
      (denote s.val.carrier) =
    F.fnSetValue (F.sepValue (denote (NPos (M := M))) (fun _ => True))
      (denote t.val.carrier)
  exact congrArg (F.fnSetValue (F.sepValue (denote (NPos (M := M))) (fun _ => True))) hc

end Litex
