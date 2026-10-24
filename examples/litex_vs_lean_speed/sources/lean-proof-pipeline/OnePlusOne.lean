import Lean

set_option Elab.async false

namespace ProofPipeline

theorem one_add_one : (1 : Nat) + 1 = 2 := by rfl
theorem add_one (n : Nat) : n + 1 = Nat.succ n := by rfl
theorem one_add_one_term : (1 : Nat) + 1 = 2 := @Eq.refl Nat 2

#print one_add_one
#print add_one

set_option pp.all true in
#print one_add_one

set_option pp.all true in
#print add_one

#print one_add_one_term
#check @Eq.refl
#reduce (1 : Nat) + 1
#print Nat.add
#print axioms one_add_one
#print axioms add_one
#print axioms one_add_one_term

open Lean Elab Command in
elab "#raw_proof " n:ident : command => do
  let ci ← getConstInfo n.getId
  match ci with
  | .thmInfo ti =>
    logInfo m!"RAW_TYPE {repr ti.type}"
    logInfo m!"RAW_PROOF {repr ti.value}"
  | _ => throwError "expected a theorem"

#raw_proof ProofPipeline.one_add_one
#raw_proof ProofPipeline.add_one

end ProofPipeline
