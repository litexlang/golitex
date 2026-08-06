# Litex Blueprint: Bringing Verifiable Mathematics Closer to Everyday Mathematical Writing

Jiachen Shen and The Litex Team, 2026-07-24. Email: litexlang@outlook.com

Website: https://litexlang.com/doc/Litex_Blueprint

## Background

The arrival of AI is rapidly increasing the amount of generated mathematical proof, making verification an increasingly important bottleneck. Litex tests the following hypothesis: can we design a formal language that, like everyday mathematics, centers objects and facts while still being checked rigorously by a machine? Can such a language make the distance between writing mathematics and verifying it short enough that users can genuinely understand the formal tool they are using, its trusted boundary, and exactly why a conclusion was accepted? The design of the Litex language and its output should serve this stricter goal.

Litex develops this hypothesis in public, so the repository intentionally exposes experiments and unfinished work as well as checked results. Public availability is not a completion claim; each claim should be read against its current tests, dated status, trust boundary, and known limitations.

## Starting from the Everyday Mathematical Workflow

Existing formal languages have achieved enormous success. Mathematicians, however, do not usually begin by creating a proof state and then translating every step into a sequence of commands. A more typical process is:

1. Write down the objects, definitions, and conditions.
2. Recognize a familiar pattern.
3. Use a known fact, definition, or computation to write the next fact.
4. Add that fact to the context for subsequent reasoning.

Litex turns this everyday workflow into its default execution model. The whole process can be summarized as follows:

> **Litex: the user states what should hold → the checker searches for proof support → the output explains why and how the statement was verified → the verified fact enlarges the context → the proof grows bottom-up.**
>
> **Lean tactics: the theorem states the final Goal → the user states how to rewrite, decompose, or close it → Infoview shows which Goals remain → tactics construct the proof term → the kernel checks the term.**

Along these two axes, the default interactions point in opposite directions.

1. **Litex grows bottom-up; Lean tactic proofs work top-down.** In Litex, each verified fact extends the context until the accumulated facts support a conclusion. Lean tactic proofs normally begin with the final Goal and work backward, transforming it into smaller Goals until they can be closed by known facts.
2. **Litex users state *what* should hold; Lean tactic users state *how* the Goal should be proved.** The Litex checker searches for matching proof support and explains the route it found. Lean tactic elaboration follows the user's proof instructions to construct the corresponding proof term, the server shows the resulting Goals, and the kernel checks the term.

> A complete LEGO instruction manual contains two kinds of information: first,
> how to perform the next step; and second, what the entire partially assembled
> model should look like after that step. Lean tactic source primarily records
> the first kind—how to manipulate the proof state next. Litex source primarily
> records the second—what mathematical fact has been established by that step
> of reasoning.

Lean's mechanism provides a highly flexible and general proof-programming environment. Litex deliberately chooses a narrower default interaction so that beginning a proof can be easier and the source can remain closer to ordinary textbook mathematics. This is a difference in default interface, not an absolute capability boundary: Lean also supports forward reasoning, and Litex also provides explicitly goal-directed proof forms. The comparison and five design goals below develop the similarities, differences, and tradeoffs between these two workflows.

## A Small but Complete Comparison: Uniqueness of the Identity in a Group

The group-identity example makes the two workflow differences above concrete. It shows who states the result, who supplies the proof route, and whether the proof is organized from a final Goal downward or from verified facts upward. It also presents definitions and proofs in mathematical order and treats structures and carriers explicitly as set-theoretic objects.

### Lean: An Explicit Record, Named Hypotheses, and a Proof Script

The following code retains the original `Group` record. In the original `calc`, the first line used `hright G.one` for `e = G.mul e G.one`, but that hypothesis actually gives `G.mul G.one e = G.one`. Here is a corrected version that matches the hypothesis and is accepted by Lean:

```lean
structure Group where
  Carrier : Type
  mul : Carrier → Carrier → Carrier
  one : Carrier
  inv : Carrier → Carrier
  mul_assoc : ∀ a b c : Carrier, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : Carrier, mul one a = a
  mul_one : ∀ a : Carrier, mul a one = a
  mul_left_inv : ∀ a : Carrier, mul (inv a) a = one

theorem one_unique
    (G : Group)
    (e : G.Carrier)
    (hleft : ∀ a : G.Carrier, G.mul e a = a)
    (hright : ∀ a : G.Carrier, G.mul a e = a) :
    e = G.one := by
  calc
    e = G.mul G.one e := (G.one_mul e).symm
    _ = G.one := hright G.one
```

This is good Lean code. It makes the steps required by the proof term explicit. The hypothesis `hleft` remains because the statement says that `e` is a two-sided identity, although the conclusion itself only needs the right-identity law for the candidate `e` and the left-identity law for `G.one`.

The Litex version below states the same structure and uniqueness argument in a
different surface. The five sections following both snippets explain the
design contrast once and tie each general point back to this example.

### Litex: Structures, Local Facts, and Conclusions in Mathematical Order

The following Litex snippet has been verified with the Litex runner.

```litex
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one

forall s nonempty_set, G &Group<s>, identity s:
    forall a s:
        G.mul(identity, a) = a
        G.mul(a, identity) = a
    =>:
        identity = G.mul(G.one, identity) = G.one
```

The interpretation of this example is distributed through the five sections
below, so the comparison and the design argument stay aligned without a
second five-point summary here.

## How Litex Pursues These Goals

### 1. Users State Results Directly; the System Searches for Proof Support

What Litex first changes is not code length but the division of labor between user and system. The user writes results that should hold, such as `1 + 1 = 2`, the union of finite sets being finite, or `x^2 >= 0`. Litex first checks that their objects are well-defined, then searches builtin rules, known facts, and known universally quantified facts for support. In typical Lean tactic interaction, the conclusion is first given as a Goal; the user then specifies which facts to invoke and how to rewrite or decompose the Goal, and the system constructs the complete proof accordingly.

| Default interaction | User source primarily states | Interactive output primarily supplies |
|---|---|---|
| Lean tactics + server/Infoview | How to rewrite, decompose, or close the current Goal | Which Goals remain after each step |
| Litex facts + checker output | The next fact or result that should hold | Why that fact passed and its immediate verification source |

In short, Lean tactic source emphasizes *how*, while server output supplies *what remains*; Litex source emphasizes *what*, while checker output supplies *why/how*. This describes the center of gravity of the two default interactions, not an exclusive capability boundary: Lean can state intermediate results explicitly, and Litex can organize proofs around explicit Goals.

Litex currently encodes hundreds of small, concrete mathematical patterns as builtin verification rules, covering common cases involving numbers, equality, order, sets, functions, tuples, and membership. These rules are not intended to form an invisible “big automation button.” Each rule should have a readable mathematical meaning, an implementation, tests, and a checkable explanation in the output. The precise rule catalog will evolve, so the number of rules is not treated here as a stable headline metric.

Providing a corresponding Lean theorem or code explanation for every builtin rule is a valuable audit target, but a rule should not be treated as formally justified merely because it looks intuitive. The trusted boundary, rule implementations, regression tests, and independent cross-checking all need to remain visible and continue to improve.

When doing mathematics, people often begin by recognizing a pattern: the current expression is the same as an earlier one, or differs only by substitution, unfolding, or instantiation. Mathematical reasoning is rarely driven primarily by remembering the internal name of every auxiliary lemma.

Litex therefore places verified facts in the current context and tries to match and substitute them. A known `forall` fact can be instantiated when its parameter conditions are satisfied, and a known equality can help match a larger expression. This is not “guessing a proof”: every successful step must still pass the rule and context checks. Litex retains named theorems and explicit `by thm` invocations for results that are large, expensive, or whose dependencies should remain visible to the reader.

In the `Group` example, the laws are stated in `<=>:` and the uniqueness
argument is stated as `identity = G.mul(G.one, identity) = G.one`. The checker
finds the relevant identity-law instances and equality direction, so the
source records what should hold while the verification route supplies why.

### 2. Present Set-Theoretic Objects at the Surface Instead of Requiring Users to Learn Type Universes First

The Litex surface language presents objects, sets, membership, functions, and structures as ordinary mathematical objects: objects belong to sets; structures are subsets of Cartesian products with named views; and properties are expressed by predicates. The phrase `s set` states the mathematical judgment that “`s` is a set.” It does not add another user-facing layer of `Type`, universes, or proof terms that must be operated explicitly.

This does not mean that the language imposes no constraints. Function domains, result sets, structure fields, and set membership are still checked; these constraints are simply written where mathematicians would normally write them. Litex also retains parameterized constructions such as `template`, because ordinary mathematics genuinely needs families of objects indexed by carriers, parameters, or assumptions. Litex does not present itself as a complete dependent type theory.

The `Group` example makes this surface concrete: `s nonempty_set` introduces
the carrier, `identity s` states membership, and `G &Group<s>` places the
structure on that set. The carrier constraints remain explicit without first
presenting them as a user-managed universe hierarchy.

### 3. Shape the Syntax Around Mathematical Reasoning, Not Functional Programming

A Litex file has only a few core kinds of action: define an object or concept, check a fact, check that an object is well-defined, and provide a witness, case split, or induction when needed. In the ordinary path, users can write in textbook order: a definition, conditions, a local conclusion, the next local conclusion, and a theorem.

This does not mean that Litex never needs structured proofs. Existence, contradiction, case analysis, and induction still require the corresponding mathematical moves to be stated explicitly. Routine computation, substitution, and use of known laws, however, need not be decomposed into a pipeline of “set a goal, invoke a tactic, name an intermediate result, invoke another tactic.” The language should not force users to reorder a clear mathematical narrative merely to follow the construction order of a functional proof term.

In the `Group` declaration, multiplication is written as the binary function
`mul fn(x, y s) s` and used as `G.mul(x, y)`. The definition therefore exposes
the familiar mathematical arity instead of requiring the user-facing syntax
to present multiplication as a curried chain of unary functions.

### 4. Preserve Rigor While Remaining Readable and Accessible

A textbook-like surface does not lower the standard of checking. Every fact receives a result such as `true`, `unknown`, or `error`. The checking process distinguishes whether an expression is well-defined, whether the current context is sufficient, and which builtin rule, known fact, or universally quantified fact supports the conclusion. A `trust` statement remains an explicitly injected assumption rather than a proof, and builtin and inference rules remain part of the trusted computing base.

Litex is therefore not a replacement for Lean, Coq, or Isabelle. It tests a complementary interface: can a smaller, readable, fact-oriented, set-theoretic surface make it inexpensive enough for students, domain researchers, and AI agents to produce, check, and repair useful formal mathematical data? Success must be demonstrated through runnable examples, recorded failures, tests, rule audits, and independent checking—not by how natural the syntax appears.

The `Group` snippet passes only after the runner checks its fields, carrier
memberships, law instances, and both links of the equality chain. It contains
no `trust`; any such statement would instead be an explicit addition to the
trusted boundary, alongside the checker and its builtin and inference rules.

### 5. Build Proofs Bottom-Up from Verified Facts

Litex is fact-oriented. Its default unit of progress is the next mathematical fact, rather than an active Goal that every line must immediately advance. If a statement is in scope, well-defined, and justified by the current context, the checker can accept it, store it, run the applicable inference, and expose the enlarged context to later statements. A typical Litex proof therefore grows forward and bottom-up: establish facts, derive further facts, and continue until the accumulated context supports the final conclusion. A fact may help the next line, a theorem much later, or remain an independent checked result. Several branches of a mathematical development can grow separately before a later statement makes them converge.

Lean's ordinary interactive theorem proving is goal-directed and typically works backward or top-down. The final theorem first determines the expected type. Local terms and tactics are elaborated under that expectation, progressively decomposing the pending Goal into simpler subgoals until Lean can assemble the complete proof term. The contrast can be stated as two default questions: Lean asks, “What must still be proved to construct this Goal?” Litex asks, “What fact follows next from the context already established?”

This is a difference in default workflow, not an absolute expressive boundary. Lean can accumulate forward facts with `have`, local lemmas, and independent top-level theorems; Litex can organize explicitly goal-directed work with forms such as `claim` and `thm`. The direction of development changes, not the standard of correctness: scope, well-definedness, and mathematical justification remain mandatory for every accepted Litex fact.

The following local-rewriting example makes this difference in direction more concrete. In Lean, the user starts from the pending Goal, and each `rw` specifies which fact to invoke and in which direction to match and replace:

```lean
-- Using facts from the local context.
example (a b c d g f : ℝ) (h : a * b = c * d) (h' : g = f) :
    a * (b * g) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

The corresponding Litex proof reverses Lean's four Goal transformations into one equality chain. It starts from the right-hand side of the Goal, `c * (d * f)`, states the intermediate results in turn, and ends at the left-hand side, `a * (b * g)`:

```litex
claim:
    ?forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    c * (d * f) = (c * d) * f = (a * b) * f = a * (b * f) = a * (b * g)
```

1. The first equality corresponds to `rw [mul_assoc]`.
2. The second equality corresponds to `rw [h]`.
3. The third equality corresponds to `rw [← mul_assoc]`.
4. The fourth equality corresponds to `rw [h']`.

These four equalities correspond to Lean's four `rw` commands in reverse order. The Lean code tells the system which fact to invoke next and in which direction to rewrite the Goal. The Litex code instead tells the system which important intermediate results should appear if the reasoning succeeds. The checker then looks for support for each adjacent equality in the current context, equality matching, and structural rules.

The user therefore does not have to recall a library identifier such as `mul_assoc` or explicitly orchestrate the order and direction in which `h`, `h'`, and associativity are used. Instead, the user writes a mathematically meaningful chain of intermediate results. If one jump is too large, the added guidance is another intermediate expression rather than a step-by-step search instruction. This example deliberately avoids automation that could normalize the whole algebraic goal at once: the point is to compare the default direction of interaction, not code length.

A completely non-computational example transports membership along set inclusions. Lean starts from the Goal `x ∈ c` and uses `apply` to state, step by step, how it should be proved:

```lean
import Mathlib

example {α : Type} {A B c : Set α}
    (hAB : A ⊆ B) (hBc : B ⊆ c)
    {x : α} (hx : x ∈ A) :
    x ∈ c := by
  apply hBc
  apply hAB
  exact hx
```

Litex instead directly states the intermediate and final results that should be established, and the checker searches the current context for their support:

```litex
forall A, B, c set, x A:
    A $subset B
    B $subset c
    =>:
        x $in B
        x $in c
```

The corresponding runner trace supplies the verification support omitted from
the source. Only the fields directly relevant to the two conclusions are shown
here:

```text
"conclusions": [
  {
    "statement": "x $in B",
    "why_verified": {
      "type": "builtin rule",
      "rule": "membership through a known direct set inclusion"
    }
  },
  {
    "statement": "x $in c",
    "why_verified": {
      "type": "builtin rule",
      "rule": "membership through a known direct set inclusion"
    }
  }
]
```

In Lean, the user tells the system how to take the next proof step. The system decomposes `x ∈ c` backward into `x ∈ B`, then into the known fact `x ∈ A`. In Litex, the user tells the system what the next result is. Starting from `x ∈ A`, the checker confirms `x ∈ B` and then `x ∈ c`. The former typically unfolds backward from a complete Goal and is top-down; the latter accumulates verified facts toward the conclusion and is bottom-up.

The Lean source does not state its intermediate Goals as mathematical results
inside the theorem. As the cursor moves forward through the tactics, Infoview
supplies that missing part. The local context, which is unchanged at each step,
is omitted below:

```text
After entering `by`:
⊢ x ∈ c

After `apply hBc`:
⊢ x ∈ B

After `apply hAB`:
⊢ x ∈ A

After `exact hx`:
no goals
```

The two outputs therefore supply exactly what their respective sources leave
unstated. The Litex source already contains `x $in B` and `x $in c`, so the
runner reports why they passed. The Lean source states how to manipulate the
proof state, so Infoview reports which Goal remains after each step.

Together, the two examples make “bottom-up” concrete. Lean begins with a complete Goal and rewrites or decomposes it until it reaches known facts. Litex establishes checkable equalities or membership facts until they support the final conclusion. Ordinary mathematical writing often works similarly: definitions, known facts, and decisive intermediate results are recorded first and then converge on a conclusion, rather than always decomposing a formal Goal backward into subgoals. For both people and AI systems, proposing meaningful intermediate expressions is often more natural than continually remembering library identifiers such as `pow_two` and `mul_assoc` together with their invocation directions. This does not mean that every mathematical discovery or proof is strictly bottom-up: induction, contradiction, existence proofs, and complex theorems may still need an explicit goal structure.

Returning to `Group`, the structure laws are verified and stored when the
concept is defined; the candidate identity laws later enlarge the context;
only then is the uniqueness chain checked. That sequence is the same
bottom-up pattern illustrated by the calculation and inclusion examples.

## Conclusions

For an overview of the components of the Litex system, see the [Litex System Map](https://litexlang.com/doc/Litex_System_Map). To try Litex examples and inspect the generated output and knowledge graphs, visit [litexlang.com](https://litexlang.com). For the Litex kernel, see the [golitex repository](https://github.com/litexlang/golitex).

Litex should not promise to “omit proof.” Its intended promise is both stricter and more modest: let users first write the mathematical facts they actually mean, then let the machine expose the verification, provenance, and boundaries clearly.

> **Put sharply: the familiar Lean tactic workflow can feel like being forced to read a mathematics book from its last page, or to write a paper from its last page—first fix the final Goal, then work backward to reconstruct everything that must come before it.**

For mathematical exploration, learning, and textbook-style exposition, this order can feel deeply unnatural. Litex makes a deliberate design judgment that it should not be the only or default way to write formal mathematics.

> **Equally sharply: Litex's biggest first-principles problem is that its trusted kernel is too large. Litex moves hundreds of common proof patterns into builtin and inference rules, shifting work from the user's proof script into the trusted computing base. The proof work did not disappear; the system absorbed it. Litex code must be compilable to Lean and checked there if its correctness is to be guaranteed.**

For this reason, Litex needs to accumulate experience toward a compilation path to Lean. The current repository keeps only a narrow experiment: it handles verified rational equalities over `R`, recursively constructs numerator and denominator expressions, and emits Lean checked by `ring`, or by `field_simp` followed by `ring`. It is not yet a compiler for general Litex statements or builtin rules. The long-term target remains to check source with Litex, generate an equivalent Lean statement and proof, and have Lean check that result independently.

Another major difference is that **Litex users state *what* should hold, while
Lean tactic users state *how* the Goal should be proved.** The Litex checker
searches for proof support that matches the result and explains the verification
route it found. Lean tactic elaboration follows the user's proof instructions to
construct the corresponding proof term; the server displays the resulting
Goals, and the kernel checks the term.

As collaboration between humans and AI makes it possible to create an
increasing body of mathematical knowledge, formal systems should explore more
than one way to write and verify that knowledge. At the level of their default
interaction directions, Litex can in a limited sense be viewed as “the opposite
of Lean”: Lean tactics typically begin from a final Goal and ask the user how to
construct its proof, while Litex typically begins from established facts and
asks the user what should follow next, leaving the checker to find and explain
the support. This is not an attempt to replace Lean. It is another direction
worth practicing and testing for how humans and AI might write formal
mathematics together.
