# Introduction to Litex Builtin Features

**Builtin features** are the parts of Litex that come with the system: a **shared semantic layer** that names ordinary mathematical objects, spells out what you can **write** in a file, decides which goals the **checker** can close on its own, extends the context after facts are **stored**, and lists the **atomic proposition forms** (`$…` and friends) the surface language treats as single steps.

They are not a grab bag of tricks. They answer four coupled questions:

1. **What can you talk about?** — Standard sorts and constructors (numbers, sets, tuples, products, function spaces, sequences, matrices, families, …) and how they are meant to behave.  
2. **What can you write at top level?** — Definitions, declarations, proof blocks, imports, and tactic-shaped phrases that organize checks.  
3. **What can the verifier do automatically while checking?** — Builtin **verification rules** that discharge goals matching fixed patterns (algebra, order, sets, logic glue users should not have to re-prove by hand).  
4. **What is added after a fact is accepted?** — Builtin **inference**: extra facts or bookkeeping derived from what you just proved or asserted, so later lines can see typical consequences (membership unfoldings, subset consequences, small order facts, …).

Each builtin rule or definition is usually **easy to read in isolation**. The real size comes from **how many combinations** arise once equality, membership, products, `fn`, ranges, positivity cones, and so on all meet in real proofs. Builtin features exist so that bulk stays in the **language**, not on every user’s TODO list.

The best way to understand the proof process is to read the message printed out after a statement is executed: it helps you know how a statement is executed and effects it has on the context.

---

## How this folder is organized

| Topic | Document |
|--------|-----------|
| Mathematical sorts, literals, and builtin objects | [Builtin_Objects.md](Builtin_Objects.md) |
| Surface forms: statements you can use in scripts | [Builtin_Statements.md](Builtin_Statements.md) |
| Atomic proposition shapes (`$is_set`, `$in`, comparisons, …) | [Builtin_Props.md](Builtin_Props.md) |
| Goals closed **during** verification | [Builtin_Verification_Rules.md](Builtin_Verification_Rules.md) |
| Facts and side information added **after** storage | [Builtin_Inference.md](Builtin_Inference.md) |

Together, these describe **what Litex already knows** before your own `prop`s and `forall` theorems enlarge the theory. For how that builtin world fits into the bigger proof story (user definitions, `forall`, traces), see [Mechanics of Litex](../Mechanics_of_Litex.md).

