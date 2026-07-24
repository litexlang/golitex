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

Ordinary handwritten mathematics can of course omit steps, so “like everyday mathematics” cannot mean “giving up rigor.” Litex aims to do the opposite: preserve this order of writing while asking the checker to verify every fact, the well-definedness of every object, and every reuse of a matching fact.

## A Small but Complete Comparison: Uniqueness of the Identity in a Group

This example illustrates three points at once: local facts need not all be named; definitions and proofs appear in mathematical order; and structures and carriers are presented explicitly as set-theoretic objects.

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

This example clearly motivates the goals that Litex is trying to achieve.

1. Write facts before orchestrating a proof script

Names such as `mul_assoc`, `one_mul`, and `hleft` are required to refer to the corresponding facts in this Lean code. As their number grows, they become harder to remember. Can some of these names be made unnecessary?

2. Reuse the shape of a fact, not only its theorem name

The expressions `:= (G.one_mul e).symm` and `:= hright G.one` explicitly explain why `e = G.mul G.one e` and `_ = G.one` are valid. Can the user avoid writing these invocations when the relevant fact already has the right shape? Composing such steps is not always obvious and normally requires some familiarity with the system.

3. Present set-theoretic objects at the surface instead of requiring users to learn type universes first

The declaration `Carrier : Type` places the carrier in Lean's type-theoretic setting, where sets are defined relative to an underlying type. Could the concept of a group instead be presented directly over a set? Dependent types and sets are substantially different, and a set-based surface may be easier for many readers to understand.

4. Make the mathematical statement, rather than functional-program structure, the subject

The declaration `mul : Carrier → Carrier → Carrier` uses a functional-programming presentation: a binary function is represented as a curried sequence of unary functions. Could the language express this using notation closer to ordinary mathematics?

5. Derive rigor from a checkable process, and remain a familiar appearance

Lean uses type theory and explicit proof construction to make the group definition and proof rigorous. As a mainstream formal language, Lean is famous for its solidness and community effort. But could a formal language allow the user to enter the mathematical definition and facts while the system fills in some routine proof steps? Much of the text above follows the proof assistant's construction pattern rather than the presentation normally found in a textbook.

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

forall s nonempty_set, G &Group<s>, e s:
    forall a s:
        G.mul(e, a) = a
        G.mul(a, e) = a
    =>:
        e = G.mul(G.one, e) = G.one
```

This example shows concretely how Litex pursues the five goals above.

1. Write facts before orchestrating a proof script

The group laws are written directly in the `<=>:` section of the structure definition; they do not first need individual names. The uniqueness proof also follows the mathematical narrative: state that the candidate `e` satisfies the left- and right-identity laws, then write the equality chain `e = G.mul(G.one, e) = G.one`. The user submits local facts and a conclusion to be checked, rather than a sequence of commands that manipulate a proof state.

2. Reuse the shape of a fact, not only its theorem name

The checker can recognize `G.mul(G.one, e) = e` from the group identity law and use symmetry for the first step of the equality chain. It can also instantiate the candidate identity law `G.mul(a, e) = a` at `a = G.one` to obtain the second step. No names such as `one_mul` or `hright` are invoked. Reuse happens by matching verified `forall` facts against the current expression.

3. Present set-theoretic objects at the surface instead of requiring users to learn type universes first

The phrase `s nonempty_set` says directly that the carrier `s` is a nonempty set; `e s` says that `e` belongs to `s`; and `G &Group<s>` says that `G` is a group structure on `s`. The declarations `one s`, `inv fn(x s) s`, and `mul fn(x, y s) s` state the domains and codomains of the constant, inverse operation, and multiplication in terms of the sets containing their objects. The user sees sets, elements, functions, and structures rather than a `Type` or universe hierarchy that must first be manipulated.

4. Make the mathematical statement, rather than functional-program structure, the subject

Binary multiplication is declared as `mul fn(x, y s) s` and applied in the familiar form `G.mul(x, y)`; it need not be presented as the curried function `Carrier → Carrier → Carrier`. The overall structure of the code is also mathematical: define a group, suppose another element satisfies the identity laws, and conclude that it equals the group's identity. The syntax follows the hierarchy of definitions, assumptions, and conclusions rather than the construction of a functional proof term.

5. Derive rigor from a checkable process, and remain a familiar appearance

The snippet is accepted by the Litex runner not merely because it resembles a correct textbook proof. The checker must still verify that `G.one`, `e`, and every multiplication lie in the appropriate set; that the structure laws can be instantiated with the current arguments; and that the two equality steps are each supported by established facts. What is omitted is the user's manual naming and proof-script orchestration, not the checks themselves. The trusted boundary still includes the Litex checker, its builtin and inference rules, and any explicitly introduced `trust` assumptions.

## How Litex Pursues These Goals

### 1. Write Facts Before Orchestrating a Proof Script

Common facts such as `1 + 1 = 2`, the union of finite sets being finite, or `x^2 >= 0` should not require users to recall a lemma name and repeat a tactic sequence each time. The user writes a fact. Litex first checks that its objects are well-defined, then tries builtin rules, known facts, and known universally quantified facts.

Litex currently encodes hundreds of small, concrete mathematical patterns as builtin verification rules, covering common cases involving numbers, equality, order, sets, functions, tuples, and membership. These rules are not intended to form an invisible “big automation button.” Each rule should have a readable mathematical meaning, an implementation, tests, and a checkable explanation in the output. The precise rule catalog will evolve, so the number of rules is not treated here as a stable headline metric.

Providing a corresponding Lean theorem or code explanation for every builtin rule is a valuable audit target, but a rule should not be treated as formally justified merely because it looks intuitive. The trusted boundary, rule implementations, regression tests, and independent cross-checking all need to remain visible and continue to improve.

### 2. Reuse the Shape of a Fact, Not Only Its Theorem Name

When doing mathematics, people often begin by recognizing a pattern: the current expression is the same as an earlier one, or differs only by substitution, unfolding, or instantiation. Mathematical reasoning is rarely driven primarily by remembering the internal name of every auxiliary lemma.

Litex therefore places verified facts in the current context and tries to match and substitute them. A known `forall` fact can be instantiated when its parameter conditions are satisfied, and a known equality can help match a larger expression. This is not “guessing a proof”: every successful step must still pass the rule and context checks. Litex retains named theorems and explicit `by thm` invocations for results that are large, expensive, or whose dependencies should remain visible to the reader.

### 3. Present Set-Theoretic Objects at the Surface Instead of Requiring Users to Learn Type Universes First

The Litex surface language presents objects, sets, membership, functions, and structures as ordinary mathematical objects: objects belong to sets; structures are subsets of Cartesian products with named views; and properties are expressed by predicates. The phrase `s set` states the mathematical judgment that “`s` is a set.” It does not add another user-facing layer of `Type`, universes, or proof terms that must be operated explicitly.

This does not mean that the language imposes no constraints. Function domains, result sets, structure fields, and set membership are still checked; these constraints are simply written where mathematicians would normally write them. Litex also retains parameterized constructions such as `template`, because ordinary mathematics genuinely needs families of objects indexed by carriers, parameters, or assumptions. Litex does not present itself as a complete dependent type theory.

### 4. Make the Mathematical Statement, Rather Than Functional-Program Structure, the Subject

A Litex file has only a few core kinds of action: define an object or concept, check a fact, check that an object is well-defined, and provide a witness, case split, or induction when needed. In the ordinary path, users can write in textbook order: a definition, conditions, a local conclusion, the next local conclusion, and a theorem.

This does not mean that Litex never needs structured proofs. Existence, contradiction, case analysis, and induction still require the corresponding mathematical moves to be stated explicitly. Routine computation, substitution, and use of known laws, however, need not be decomposed into a pipeline of “set a goal, invoke a tactic, name an intermediate result, invoke another tactic.” The language should not force users to reorder a clear mathematical narrative merely to follow the construction order of a functional proof term.

### 5. Derive Rigor from a Checkable Process, and remain a Familiar Appearance

A textbook-like surface does not lower the standard of checking. Every fact receives a result such as `true`, `unknown`, or `error`. The checking process distinguishes whether an expression is well-defined, whether the current context is sufficient, and which builtin rule, known fact, or universally quantified fact supports the conclusion. A `trust` statement remains an explicitly injected assumption rather than a proof, and builtin and inference rules remain part of the trusted computing base.

Litex is therefore not a replacement for Lean, Coq, or Isabelle. It tests a complementary interface: can a smaller, readable, fact-oriented, set-theoretic surface make it inexpensive enough for students, domain researchers, and AI agents to produce, check, and repair useful formal mathematical data? Success must be demonstrated through runnable examples, recorded failures, tests, rule audits, and independent checking—not by how natural the syntax appears.

## Next Steps

For an overview of the components of the Litex system, see the [Litex System Map](https://litexlang.com/doc/Litex_System_Map). To try Litex examples and inspect the generated output and knowledge graphs, visit [litexlang.com](https://litexlang.com). For the Litex kernel, see the [golitex repository](https://github.com/litexlang/golitex).

Litex should not promise to “omit proof.” Its intended promise is both stricter and more modest: let users first write the mathematical facts they actually mean, then let the machine expose the verification, provenance, and boundaries clearly.

Litex is also designing and implementing a compilation path to Lean. For supported Litex content, the goal is to check it with Litex, generate Lean, and then check the result independently with Lean. Readers therefore need not treat the number of builtin rules as an automatic reason to dismiss Litex before examining it. By design, each builtin rule is a small, concrete mathematical pattern that can usually correspond to a small number of ordinary Lean proof steps or tactic combinations. This compiler remains under development. Until it covers all required rules, assessments of reliability must continue to rely on inspectable rule implementations, verifier output, tests, and explicit `trust` boundaries. This is how Litex aims to preserve meaningful, auditable rigor despite having a comparatively large trusted kernel.
