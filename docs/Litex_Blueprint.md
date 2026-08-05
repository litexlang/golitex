# Litex Blueprint: Bringing Verifiable Mathematics Closer to Everyday Mathematical Writing

Jiachen Shen and The Litex Team, 2026-07-24. Email: litexlang@outlook.com

Website: https://litexlang.com/doc/Litex_Blueprint

## Background

The arrival of AI is rapidly increasing the amount of generated mathematical proof, making verification an increasingly important bottleneck. Litex tests the following hypothesis: can we design a formal language that, like everyday mathematics, centers objects and facts while still being checked rigorously by a machine? Can such a language make the distance between writing mathematics and verifying it short enough that users can genuinely understand the formal tool they are using, its trusted boundary, and exactly why a conclusion was accepted? The design of the Litex language and its output should serve this stricter goal.

## Starting from the Everyday Mathematical Workflow

Existing formal languages have achieved enormous success. Mathematicians, however, do not usually begin by creating a proof state and then translating every step into a sequence of commands. A more typical process is:

1. Write down the objects, definitions, and conditions.
2. Recognize a familiar pattern.
3. Use a known fact, definition, or computation to write the next fact.
4. Add that fact to the context for subsequent reasoning.

Litex turns this everyday workflow into its default execution model. The user writes a result that should hold; the checker verifies that its objects are well-defined, searches builtin rules and the verified context for proof support, reports why the result was accepted, and then adds the verified fact to the context available to later statements. The central chain is:

> **Litex: the user states what should hold → the checker searches for proof support → the output explains why and how the statement was verified → the verified fact enlarges the context → the proof grows bottom-up.**
>
> **Lean tactics: the theorem states the final Goal → the user states how to rewrite, decompose, or close it → Infoview shows which Goals remain → tactics construct the proof term → the kernel checks the term.**

Along these two axes, the default interactions point in opposite directions.

1. **Litex grows bottom-up; Lean tactic proofs work top-down.** In Litex, each verified fact extends the context until the accumulated facts support a conclusion. Lean tactic proofs normally begin with the final Goal and work backward, transforming it into smaller Goals until they can be closed by known facts.
2. **Litex users state *what* should hold; Lean tactic users state *how* the Goal should be proved.** The Litex checker searches for matching proof support and explains the route it found. Lean tactic elaboration follows the user's proof instructions to construct the corresponding proof term, the server shows the resulting Goals, and the kernel checks the term.

Lean's mechanism provides a highly flexible and general proof-programming environment. Litex deliberately chooses a narrower default interaction so that beginning a proof can be easier and the source can remain closer to ordinary textbook mathematics. This is a difference in default interface, not an absolute capability boundary: Lean supports forward reasoning, and Litex also provides explicitly goal-directed proof forms. The comparison and design goals below develop these two workflows, their common ground, and their different tradeoffs in detail.

Ordinary handwritten mathematics can of course omit steps, so “like everyday mathematics” cannot mean “giving up rigor.” Litex aims to do the opposite: preserve this order of writing while asking the checker to verify every fact, the well-definedness of every object, and every reuse of a matching fact.

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

Read through the two workflow differences above, this example motivates five connected design goals rather than a collection of independent syntax features.

1. Users state results directly; the system searches for proof support

This is the most fundamental difference in division of labor between Litex and typical Lean tactic interaction. A Litex user primarily states what the result should be; the checker then searches builtin rules, the current context, and known universal facts for proof support by matching their shapes. In a Lean tactic proof, the user primarily states how the current Goal should be rewritten or decomposed; the system follows those instructions to construct and check the final proof term.

This division of labor also makes the two interactive outputs approximately dual. Tactics in Lean source primarily say how to advance the proof, so the Lean server's [Infoview](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Reading-Proof-States/) shows which Goals remain after the tactic at the cursor. Litex source already states what should be proved, so Litex output primarily supplies the other half: which builtin rule, known fact, or `forall` instance verified that fact.

In the Lean code above, `(G.one_mul e).symm` and `hright G.one` explicitly specify which fact to use next, how to instantiate it, and in which direction to use it. Litex instead aims to let the user state mathematically meaningful intermediate and final results, leaving the checker to identify which verified facts support them. Reuse by shape is the mechanism that implements this division of labor, not the final objective itself.

2. Present set-theoretic objects at the surface instead of requiring users to learn type universes first

The declaration `Carrier : Type` places the carrier in Lean's type-theoretic setting, where sets are defined relative to an underlying type. Could the concept of a group instead be presented directly over a set? Dependent types and sets are substantially different, and a set-based surface may be easier for many readers to understand.

3. Shape the syntax around mathematical reasoning, not functional programming

The declaration `mul : Carrier → Carrier → Carrier` uses a functional-programming presentation: a binary function is represented as a curried sequence of unary functions. Could the language express this using notation closer to ordinary mathematics?

4. Derive rigor from a checkable process, and remain a familiar appearance

Lean uses type theory and explicit proof construction to make the group definition and proof rigorous. As a mainstream formal language, Lean is famous for its solidness and community effort. But could a formal language allow the user to enter the mathematical definition and facts while the system fills in some routine proof steps? Much of the text above follows the proof assistant's construction pattern rather than the presentation normally found in a textbook.

5. Build proofs bottom-up from verified facts

Must proof development always begin with a final Goal and work backward? Could each well-defined, justified fact enter the current context as soon as it is available, allowing the context to grow forward until it contains enough information for the final conclusion? Could several mathematical branches develop independently and converge only when their relationship becomes clear?

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

This example shows concretely how Litex pursues the five goals above.

1. Users state results directly; the system searches for proof support

The group laws are written directly in the `<=>:` section of the structure definition; they do not first need individual names. The uniqueness proof also follows the mathematical narrative: the user directly states that the candidate `identity` satisfies the left- and right-identity laws, then states the result chain `identity = G.mul(G.one, identity) = G.one`. The user submits mathematical results that should hold, rather than a sequence of commands that manipulate a proof state.

The checker can recognize `G.mul(G.one, identity) = identity` from the group identity law and use symmetry for the first step of the equality chain. It can also instantiate the candidate identity law `G.mul(a, identity) = a` at `a = G.one` to obtain the second step. No names such as `one_mul` or `hright` are invoked. Reuse happens by matching verified `forall` facts against the current expression.

2. Present set-theoretic objects at the surface instead of requiring users to learn type universes first

The phrase `s nonempty_set` says directly that the carrier `s` is a nonempty set; `identity s` says that `identity` belongs to `s`; and `G &Group<s>` says that `G` is a group structure on `s`. The declarations `one s`, `inv fn(x s) s`, and `mul fn(x, y s) s` state the domains and codomains of the constant, inverse operation, and multiplication in terms of the sets containing their objects. The user sees sets, elements, functions, and structures rather than a `Type` or universe hierarchy that must first be manipulated.

3. Shape the syntax around mathematical reasoning, not functional programming

Binary multiplication is declared as `mul fn(x, y s) s` and applied in the familiar form `G.mul(x, y)`; it need not be presented as the curried function `Carrier → Carrier → Carrier`. The overall structure of the code is also mathematical: define a group, suppose another element satisfies the identity laws, and conclude that it equals the group's identity. The syntax follows the hierarchy of definitions, assumptions, and conclusions rather than the construction of a functional proof term.

4. Derive rigor from a checkable process, and remain a familiar appearance

The snippet is accepted by the Litex runner not merely because it resembles a correct textbook proof. The checker must still verify that `G.one`, `identity`, and every multiplication lie in the appropriate set; that the structure laws can be instantiated with the current arguments; and that the two equality steps are each supported by established facts. What is omitted is the user's manual naming and proof-script orchestration, not the checks themselves. The trusted boundary still includes the Litex checker, its builtin and inference rules, and any explicitly introduced `trust` assumptions.

5. Build proofs bottom-up from verified facts

Litex is fact-oriented: its default unit of progress is the next mathematical fact, not an active Goal waiting to be reduced. The structure laws are accepted and stored when the `Group` concept is defined. Later statements can use those laws, add further facts, and strengthen the verified context. Once the context contains enough information, the identity-uniqueness conclusion can be stated and checked. In this sense, a typical Litex development proceeds forward and bottom-up: verified facts accumulate until they support the final conclusion. Different mathematical branches may grow independently before a later statement brings them together.

Lean's ordinary interactive theorem proving is goal-directed and typically proceeds backward or top-down. The final theorem first supplies an expected type; local terms and tactics such as `intro`, `apply`, and `refine` then analyze that Goal and reduce it to simpler subgoals until a complete proof term has been constructed. Litex instead asks by default: what is the next fact justified by the current context? Lean asks by default: what remains to be constructed in order to prove the current Goal?

This is a difference in default proof organization, not an absolute boundary between the languages. Lean supports forward reasoning through `have`, local lemmas, and independent theorems; Litex also provides goal-bearing forms such as `claim` and `thm`. Nor does bottom-up development weaken correctness requirements: every Litex fact must still be in scope, well-defined, and mathematically justified before it can extend the context.

## How Litex Pursues These Goals

The sections below follow the same chain. Litex first changes what the user is expected to write and what the checker is expected to supply. It then gives those user-written results a set-theoretic, mathematically shaped surface; keeps the checking route visible; and lets each verified result enlarge the context from which later results can be established.

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

### 2. Present Set-Theoretic Objects at the Surface Instead of Requiring Users to Learn Type Universes First

The Litex surface language presents objects, sets, membership, functions, and structures as ordinary mathematical objects: objects belong to sets; structures are subsets of Cartesian products with named views; and properties are expressed by predicates. The phrase `s set` states the mathematical judgment that “`s` is a set.” It does not add another user-facing layer of `Type`, universes, or proof terms that must be operated explicitly.

This does not mean that the language imposes no constraints. Function domains, result sets, structure fields, and set membership are still checked; these constraints are simply written where mathematicians would normally write them. Litex also retains parameterized constructions such as `template`, because ordinary mathematics genuinely needs families of objects indexed by carriers, parameters, or assumptions. Litex does not present itself as a complete dependent type theory.

### 3. Shape the Syntax Around Mathematical Reasoning, Not Functional Programming

A Litex file has only a few core kinds of action: define an object or concept, check a fact, check that an object is well-defined, and provide a witness, case split, or induction when needed. In the ordinary path, users can write in textbook order: a definition, conditions, a local conclusion, the next local conclusion, and a theorem.

This does not mean that Litex never needs structured proofs. Existence, contradiction, case analysis, and induction still require the corresponding mathematical moves to be stated explicitly. Routine computation, substitution, and use of known laws, however, need not be decomposed into a pipeline of “set a goal, invoke a tactic, name an intermediate result, invoke another tactic.” The language should not force users to reorder a clear mathematical narrative merely to follow the construction order of a functional proof term.

### 4. Derive Rigor from a Checkable Process, and remain a Familiar Appearance

A textbook-like surface does not lower the standard of checking. Every fact receives a result such as `true`, `unknown`, or `error`. The checking process distinguishes whether an expression is well-defined, whether the current context is sufficient, and which builtin rule, known fact, or universally quantified fact supports the conclusion. A `trust` statement remains an explicitly injected assumption rather than a proof, and builtin and inference rules remain part of the trusted computing base.

Litex is therefore not a replacement for Lean, Coq, or Isabelle. It tests a complementary interface: can a smaller, readable, fact-oriented, set-theoretic surface make it inexpensive enough for students, domain researchers, and AI agents to produce, check, and repair useful formal mathematical data? Success must be demonstrated through runnable examples, recorded failures, tests, rule audits, and independent checking—not by how natural the syntax appears.

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

In Lean, the user tells the system how to take the next proof step. The system decomposes `x ∈ c` backward into `x ∈ B`, then into the known fact `x ∈ A`. In Litex, the user tells the system what the next result is. Starting from `x ∈ A`, the checker confirms `x ∈ B` and then `x ∈ c`. The former typically unfolds backward from a complete Goal and is top-down; the latter accumulates verified facts toward the conclusion and is bottom-up.

The outputs expose the part that each source leaves unstated. In Lean, as the cursor moves through these tactics, the Infoview displays `x ∈ c`, `x ∈ B`, `x ∈ A`, and finally `no goals`. In Litex, `x $in B` and `x $in c` are already present in the source; the runner output instead reports their `why_verified` fields. Here both steps are verified by the rule labeled “membership through a known direct set inclusion.”

Together, the two examples make “bottom-up” concrete. Lean begins with a complete Goal and rewrites or decomposes it until it reaches known facts. Litex establishes checkable equalities or membership facts until they support the final conclusion. Ordinary mathematical writing often works similarly: definitions, known facts, and decisive intermediate results are recorded first and then converge on a conclusion, rather than always decomposing a formal Goal backward into subgoals. For both people and AI systems, proposing meaningful intermediate expressions is often more natural than continually remembering library identifiers such as `pow_two` and `mul_assoc` together with their invocation directions. This does not mean that every mathematical discovery or proof is strictly bottom-up: induction, contradiction, existence proofs, and complex theorems may still need an explicit goal structure.

## Next Steps

For an overview of the components of the Litex system, see the [Litex System Map](https://litexlang.com/doc/Litex_System_Map). To try Litex examples and inspect the generated output and knowledge graphs, visit [litexlang.com](https://litexlang.com). For the Litex kernel, see the [golitex repository](https://github.com/litexlang/golitex).

Litex should not promise to “omit proof.” Its intended promise is both stricter and more modest: let users first write the mathematical facts they actually mean, then let the machine expose the verification, provenance, and boundaries clearly.

Litex is also designing and implementing a compilation path to Lean. For supported Litex content, the goal is to check it with Litex, generate Lean, and then check the result independently with Lean. Readers therefore need not treat the number of builtin rules as an automatic reason to dismiss Litex before examining it. By design, each builtin rule is a small, concrete mathematical pattern that can usually correspond to a small number of ordinary Lean proof steps or tactic combinations. This compiler remains under development. Until it covers all required rules, assessments of reliability must continue to rely on inspectable rule implementations, verifier output, tests, and explicit `trust` boundaries. This is how Litex aims to preserve meaningful, auditable rigor despite having a comparatively large trusted kernel.
