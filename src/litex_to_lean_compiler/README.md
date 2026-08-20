# The Two Hard Problems in the Litex-to-Lean Compiler

1. *Represent Litex mathematics in Lean, which is a theoretical problem.* The compiler must choose a representation for each mathematical concept that is consistent with Lean and Mathlib, and that will remain natural and usable in ordinary Lean developments.

The same mathematical object or statement can often be written in Lean in
several different ways. Although these representations may express the same
mathematics, choosing one of them is a long-term compiler decision: it affects
which Lean and Mathlib theorems generated code can reuse, how later Litex
features can be added, and how well the Litex and Lean ecosystems can work
together.

The most important decisions concern basic concepts such as functions, sets,
membership, and well-definedness. Litex and Lean handle these concepts in
fundamentally different ways. The compiler therefore needs a consistent
translation model for each of them. Its goal is not merely to produce Lean
code that passes today's examples, but to produce Lean representations that
remain natural and usable in ordinary Lean developments.

2. *Turn Litex kernel execution information into Lean proofs, which is a practical problem.* The Litex kernel reads what you want to prove and searches for a proof. The compiler must translate that search into Lean code, so that Lean can check the proof and use it in later developments.

The compiler must preserve the successful route of Litex verification as structured proof information and translate it into Lean code, without reconstructing the proof from display text or asking Lean to search for a different proof.

Litex verifies a formula by searching a tree. It repeatedly breaks the goal
into smaller goals and explores possible branches. When a branch succeeds,
the reason it succeeded must be returned from the leaves of the tree back to
the root. That returned information must describe which rules were used,
which facts and mathematical objects were involved, how each subgoal was
proved, and which well-definedness results were required.

The compiler must preserve this successful route as structured proof
information and translate it into Lean code. It should not reconstruct the
proof from display text or ask Lean to search for a different proof.

Litex statements return information in a similar way. As a statement is
executed, nested operations may introduce declarations, construct objects,
store facts, establish well-definedness, or change the local environment.
Those results also need to be returned compositionally and recorded with the
proof information.

The central compiler problem is therefore to design one precise structure for
the information returned by successful verification and statement execution,
and then translate that structure deterministically into Lean declarations
and proof terms.

The following sections describe the compiler's design for these two problems. 

# Representation of Litex Mathematics in Lean

# Turn Litex Kernel Execution Information into Lean Proofs