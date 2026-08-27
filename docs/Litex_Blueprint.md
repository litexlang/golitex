# Litex: A Formal Language Where Mathematics Verifies Itself

Created and maintained by Jiachen Shen.

Website: https://litexlang.com/doc/Litex_Blueprint

Chinese version: https://litexlang.com/doc/Litex中文蓝图

> **Litex is an experimental hobby project and remains in beta. Expect edge cases.**

## Table of Contents

- [Litex Blueprint Overview](#overview)
- [The Human–AI Verification Loop](#interaction-loop)
- [1. Based on Set Theory: Keep Mathematical Objects Readable](#set-theory)
- [From a Common Foundation to New Domains: Building a Mathematical Theory from the Ground Up](#group-comparison)
- [2. Fact-Oriented: Source Preserves *What Holds*](#fact-oriented)
- [3. Bottom-Up: Let Verified Facts Continue to Grow](#bottom-up)
  - [Two Directions for Developing the Same Proof: Top-Down and Bottom-Up](#two-directions)
- [4. Lean-Compatible: Independent Rechecking for Covered Paths](#compatibility)
- [From Language to Ecosystem: The Role Litex Aims to Play](#ecosystem-role)
- [Conclusion](#conclusions)

<a id="overview"></a>

## Litex Blueprint Overview

AI is rapidly lowering the cost of reasoning, mathematical proof, and scientific exploration. Humans and AI can now propose many arguments, conjectures, and technical routes in a short time. But more answers that *look right* do not automatically create more reliable knowledge. We are entering an era of **reasoning overflow and validation crisis**: candidate conclusions are growing faster than our capacity to verify them reliably.

This shift is also creating new needs for formalization in education, science, engineering, and AI review. To turn the creative capacity released by AI into trustworthy knowledge, formalization cannot remain a capability held only by a small number of specialists.

> **The next step for formal languages is not only to give existing experts stronger tools. It is also to help more people become experts.**

People who already understand a mathematical, scientific, or engineering domain should be able to turn that knowledge into formal reasoning they can express, check, and repair—and participate directly in reviewing AI-generated work.

**Litex is testing that path. It is a formal language based on set theory, oriented around facts, designed to build proof flow bottom-up, and compatible with Lean.** It lets humans and AI write mathematical facts directly and see why verification succeeds or where it stops. Litex does not aim to lower the standard of rigor. It aims to lower the barrier to reaching rigor, so that more people who understand the problem can work with AI to express, inspect, repair, and advance trustworthy reasoning.

### Two Barriers: From Understanding Mathematics to Being Able to Formalize It

The next two examples are deliberately trivial as mathematics. They are not meant to suggest that Litex can prove something Lean cannot—both are effortless for Lean—but to separate two barriers that formal-language interfaces often combine. Lean is used as the reference point because it is a mature, general, and powerful proof assistant with a large ecosystem. The comparison asks which work the default source interface assigns to users; it is not a contest over mathematical capability.

1. **The entry-knowledge barrier:** a user may already know a mathematical fact but still need to learn imports, proposition syntax, type annotations, and tactics before writing it into the system.
2. **The distance between formal representation and ordinary mathematical thought:** even after learning the tool, a rigorous general encoding may require the user to manipulate subtypes, proof arguments, or other representation mechanisms rather than write in the way they ordinarily reason about the mathematics.

These mechanisms are not defects in Lean. They support its generality, compositionality, automation, and large ecosystem. Litex explores a different front-end division of labor: mathematical conditions must remain explicit and strictly checked, while the system takes on more management of verification evidence and representation detail so that user source can stay closer to ordinary mathematics.

Start with the first barrier. Why should a user who already knows a mathematical fact need additional tool knowledge merely to place it in a formal system?

Litex:

```litex
1 + 1 = 2
```

Lean:

```lean
import Mathlib

example : (1 : ℝ) + 1 = 2 := by norm_num
```

The point is not that `1 + 1 = 2` is difficult. In the common Lean form above, the user must still know how to import `Mathlib`, how `example` declares a proposition, why `(1 : ℝ)` carries a type annotation, and how to invoke `norm_num` after `by`. These mechanisms are valuable in complex proofs and expert work, but they are tool knowledge rather than mathematical content belonging to `1 + 1 = 2`. Litex asks whether such system knowledge must remain a prerequisite when the user already understands the mathematics.

The second example goes one step further. Even after the entry-knowledge barrier has been crossed, the formal representation itself may remain distant from ordinary mathematical thought. For a function whose domain is the positive reals, one common Lean encoding is:

```lean
example
    (f : {x : ℝ // x > 0} → ℝ)
    (x : ℝ) (hx : x > 0) :
    f ⟨x, hx⟩ = f ⟨x, hx⟩ := rfl
```

The corresponding Litex is:

```litex
forall f fn(t R: t > 0) R, x R:
    x > 0
    =>:
        f(x) = f(x)
```

**This is as plain a fact as one can state: a function value equals itself.**

Yet in the Lean subtype encoding above, applying `f` requires not only `x` but also packaging the proof `hx : x > 0` into `⟨x, hx⟩`, producing `f ⟨x, hx⟩`.

This is unlike ordinary function notation: a function receives an argument, not a well-definedness certificate. Litex still checks `x > 0` strictly, but the source says only `f(x)`.

> **Users write mathematics; the system manages verification evidence. Conditions cannot be omitted, but certificates need not be threaded by hand.**

This does not lower the verification standard. It lowers the tool barrier. Good mathematical notation has always absorbed mechanical detail so that people can focus on mathematics; formal languages in the AI era need a similar abstraction layer.

The AI era also makes a subtler failure mode increasingly real. An AI can generate a mathematical proof and corresponding Lean code, and the Lean kernel can accept that code, yet later review can reveal that the proposition encoded in Lean was not the mathematics people originally intended to prove—it may omit a condition, change a quantifier, narrow the domain, or weaken the conclusion. Nothing has failed inside the Lean kernel; it correctly checked the proposition that the code actually stated. The failure is one of alignment between formal specification and mathematical intent.

Lean code is not unintelligible, but when a formal statement carries a high proof-assistant-specific reading barrier, the mathematician or domain expert who best understands the original problem may struggle to notice that *the proof is correct but the problem was encoded incorrectly*. Lowering the reading and authoring barrier is therefore not only a matter of convenience. It also lets more people who understand the problem review AI-generated formalizations.

Litex tests a hypothesis: can we lower the barrier to formalization, without lowering the verification standard, so that students, domain experts, and AI can produce machine-checkable mathematics more easily?

The path for this experiment is:

1. Based on set theory: Litex is founded on ZFC set theory and organizes mathematical objects uniformly through sets and membership. The same object can belong to multiple sets, and the language represents mathematical objects separately from facts about those objects. By comparison, Lean's `Set α` first depends on the more abstract carrier type `α : Type*`; mathematical objects and propositions are both organized by the type system, an approach with powerful generality. Litex's tradeoff is to make set theory and the common mathematical knowledge built on it clearer to express.
2. Fact-oriented: Litex source code primarily states *what mathematical facts should hold*. Based on each fact's predicate and arguments, the kernel looks for a verification route among builtin rules, previously proved facts, and equality matching. It also checks that objects and expressions are well-defined before accepting a fact. By comparison, typical Lean tactic source code primarily states *how to handle the next Goal*, while the Infoview shows which Goals remain after each operation. Lean's type system likewise checks that expressions are well-typed; the required type information, type-class instances, and proof premises enter expressions and theorem interfaces through explicit or implicit parameters.
3. Building proof flow bottom-up: A mathematical proof can start from known conditions, derive new facts, and eventually converge on the conclusion. It can also start from the final Goal and reduce it backward to known conditions. Litex defaults to the former workflow, in which the context grows forward with verified facts; common Lean tactic interactions usually adopt the latter. Neither system excludes the other direction from what it can express.
4. Lean-compatible: The goal of the Litex-to-Lean compiler is to translate verification paths already found by the Litex kernel into Lean proof terms, which the Lean kernel can then check independently. The current compiler covers only some verification paths. “Every Litex source file can be compiled to Lean” is an unfinished direction, not a capability already delivered by the beta release.

The two workflows can be simplified as follows:

```text
Lean: proposition → Goal → tactics and elaboration → proof term → kernel check
Litex: objects and facts → kernel checks and searches for justification → verified facts extend the context
```

The hope is that using Litex can feel like doing informal mathematics: users can keep their attention on mathematical objects, conditions, intermediate facts, and conclusions without first having to confront the theoretical abstractions underlying a proof assistant, unfamiliar formal syntax, or vast external libraries. Litex acts as their copilot, providing fast, local, and traceable verification feedback. *The hope is that Litex will make it easier for people who understand problems in their own domains, but are not proof-assistant specialists, to enter the world of formal reasoning.*

> **Lean supports other encodings and forms of automation as well. The comparison here concerns source interfaces, not whether the two languages can express the same proposition.**

> **This is a design direction, not a claim that the current language, standard library, or compiler is complete.**

<a id="interaction-loop"></a>

## The Human–AI Verification Loop: Write Facts and See Their Grounds and Stopping Boundary

As humans and AI generate more candidate reasoning, a formal language needs to do more than check a finished artifact: it also needs to make visible both the support for each accepted fact and the first fact that still lacks support. Litex aims to provide the following overall interaction loop: **a human or AI writes the next mathematical fact; the verifier returns the grounds on which it accepts that fact, or, when the current context is insufficient, identifies the fact at which verification stopped.**

Consider a small set-inclusion example:

```litex
forall A, B, c set, x A:
    A $subset B
    B $subset c
    =>:
        x $in B
        x $in c
```

The source states two mathematical facts directly. The current release runner records each fact together with the rule that verified it. The following excerpt keeps only the fields relevant to this example:

```text
{
  "statement": "x $in B",
  "proof": {
    "kind": "BuiltinRule",
    "diagnostic_label": "membership through a known direct set inclusion"
  }
}
{
  "statement": "x $in c",
  "proof": {
    "kind": "BuiltinRule",
    "diagnostic_label": "membership through a known direct set inclusion"
  }
}
```

The first conclusion is supported by `x $in A` and `A $subset B`. Once accepted, `x $in B` becomes available to the second conclusion, where it combines with `B $subset c` to support `x $in c`. The example exposes both sides of the interface: user source preserves *which mathematical facts should hold*, while the verification result preserves *why the system accepted them*.

Now declare another set `d`, provide no condition connecting `x` or the preceding sets to `d`, and add `x $in d` as a third conclusion. The current runner returns an `UnknownError` whose structured result identifies:

```text
"failed_prove": {
  "index": 3,
  "count": 3,
  "statement": "x $in d",
  "unknown_result": {
    "type": "atomic fact unknown",
    "goal": "x $in d"
  }
}
```

Here `unknown` does not mean that `x $in d` is false. It means that the current context and current verification capabilities did not establish it. For this single `forall` containing three conclusions, failure of the third causes the outer statement as a whole not to be written into the environment. In an incremental workflow made of separate statements or transactional attempts, previously accepted statements can instead remain as a verified prefix. “Seeing where verification stops” therefore does not mean that Litex has solved proof search, nor does it promise that every diagnostic gives a complete minimal cause. It means that both successful support and the concrete fact currently not established can become structured feedback for the next repair.

This gives humans and AI the same loop: propose the next fact, inspect its verification support or stopping point, keep accepted progress, and continue from the boundary. Four design pillars support this loop. Set theory determines the objects users face directly; fact-oriented authoring determines what source preserves; bottom-up proof flow determines how verified facts grow; and Lean compatibility provides independent rechecking and an ecosystem path for verification routes already covered by the compiler.

<details>
<summary><strong>The Same Example: What Lean's Infoview and Litex's Verification Output Show</strong></summary>

In Lean, the same set-inclusion proof begins from the final Goal `x ∈ c`, which tactics progressively reduce to an existing hypothesis:

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

The Infoview shows the Goal remaining after each tactic:

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

The Infoview clearly shows *what remains to be proved*; Litex source and the runner trace instead preserve *which mathematical facts have been established*, *why the system accepted them*, and, when verification cannot continue, the specific fact at which it stopped. Litex's default artifact is therefore closer to a proof record that humans and AI can directly read, inspect, repair, and continue; this compares default workflows and their natural artifacts, not whether Lean can express forward proofs or preserve intermediate results as lemmas.

</details>

<details>
<summary><strong>Basic Terms: Formal Language, Goal, Tactic, and Kernel</strong></summary>

- **Formal language**: A language whose syntax and meaning are governed by explicit rules and can therefore be parsed and checked by a machine. “Formal” means that expressions have precise semantics; it does not mean that the prose sounds formal. A formal language also need not be a general-purpose programming language.
- **Proof assistant**: Software that helps users express proofs, provides interactive feedback, and checks proofs mechanically. Lean is a proof assistant with general-purpose programming capabilities.
- **Goal and Infoview**: A Goal is a proposition currently waiting to be proved. The Infoview is the window in the Lean editor that displays the current Goal, local variables, and known hypotheses.
- **Context**: The variables, definitions, assumptions, and verified facts available in the current scope. Adding a new fact extends the context so that later reasoning can use it.
- **Tactic**: A command that operates on the current Goal—for example, introducing variables, rewriting by an equality, or splitting one Goal into several subgoals. A tactic describes *what to do next in the proof*; it is not itself the final proof object accepted by the kernel.
- **Proof term and elaboration**: A proof term is the complete proof object a machine can check. Elaboration is the process by which the system fills in information omitted from the source and turns user code into a complete proof term.
- **Kernel**: In Lean, the kernel is the trusted core that checks proof terms according to foundational rules. Tactics may be complex, but their results must still pass kernel checking; the kernel generally does not choose high-level proof steps for the user.
- **Kernel/verifier**: A broad term for the part of a system responsible for checking. The Litex kernel not only checks that objects are well-defined but also searches builtin rules and the current context for grounds that verify a fact. It therefore cannot be identified directly with Lean's kernel. Litex's trusted boundary—the part on whose correctness the system relies and which must be trusted—is correspondingly larger.

</details>

<details>
<summary><strong>Why Litex Was Born in the AI Era</strong></summary>

Many programming languages begin under one or a few lead designers, who also write much of the first implementation. Litex is harder: it chooses a user interface unlike those of mainstream formal languages, so many design questions have no ready-made answer. At the same time, I believe that the more work a language handles for its users, the more natural it becomes to use. The Litex verifier kernel therefore deliberately takes on substantial proof search, well-definedness checking, and evidence management. It is a large kernel by design.

In an earlier era, I could scarcely have designed the language, designed its implementation architecture, and maintained a large verifier alone; that workload is difficult for any one person to carry. AI changes the cost of implementation. Once the framework, semantics, and boundaries are explicit, language models can often generate correct or nearly correct implementations quickly, after which tests, review, and counterexamples filter out errors. This lets me concentrate more on design and acceptance. AI is not the source of correctness, but it makes a personal language project of this scale feasible for the first time.

The Litex-to-Lean compiler is intended to add another long-term safeguard: it aims to compile verification paths found by Litex into corresponding Lean proof terms, which the Lean kernel can check independently. Only paths fully covered by the compiler and actually accepted by the Lean kernel receive that relatively independent recheck. This does not automatically remove the audit burden for other Litex paths or for Litex's larger trusted implementation.

</details>

<a id="set-theory"></a>
<a id="goal-2"></a>

## 1. Based on Set Theory: Keep Mathematical Objects Readable

If formal semantics are to be both precise and directly reviewable by users of mathematics, the first design choice is what kind of mathematical objects users encounter first in source code. Litex's answer is sets, membership, and relations between sets. When the problem itself is set-theoretic, users can therefore write sets, subsets, and intersections directly, without first introducing a type that carries those sets.

The following Litex code states that intersection is monotone with respect to inclusion:

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

This is not a proof hole left to be filled; it is a complete fact submitted to the kernel for checking. Its ordinary mathematical reading is: take any member `x` of `intersect(s, u)`. Then `x` belongs to both `s` and `u`. Since `s $subset t`, it also belongs to `t`, and therefore to `intersect(t, u)`. The user states the mathematical result that should follow; the kernel searches for a verification path by unfolding intersection membership, transporting membership along a subset relation, and reassembling membership in the intersection on the right.

<details>
<summary><strong>Full comparison: how Lean develops the same set-theoretic proposition</strong></summary>

Here is the same proposition in Lean. The example comes from the set-theory chapter of the standard Lean textbook *Mathematics in Lean*.

```lean
import Mathlib.Data.Set.Lattice

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
end
```

The first layer of objects in this Lean code is not a set but `α : Type*`: only afterward are `s`, `t`, and `u` declared as values of `Set α` over that carrier type. More precisely, `Set α` in Lean is a predicate whose domain is `α`; `Type*` and its universe hierarchy provide a type-theoretic organization that is more abstract and general than sets. This design allows the same theorems to be reused over arbitrary carrier types and is an important source of Lean's expressiveness and compositionality.

Litex chooses a different task boundary. Because it takes set-theoretic objects and membership as its language surface, the language and kernel can provide specialized syntax and verification paths for high-frequency set-theoretic knowledge about sets, membership, subsets, intersections, and unions. For this task, the user need only use `set` to declare three sets and write the expected inclusion, so the code is closer to everyday set-theoretic writing and is visibly shorter.

The difference should not be reduced to “short code is necessarily stronger than long code.” Lean can prove the same proposition with a shorter proof term or with automation. The version above deliberately preserves the pedagogical route from *Mathematics in Lean*: unfold the definitions, decompose membership in the intersection, and then assemble it again. The real comparison concerns the default interface. Lean first gives a set a type-theoretic carrier, after which the user or a tactic constructs a proof. Litex instead makes common set-theoretic relations into mathematical facts the language can recognize and check directly.

</details>

This set-theoretic surface does not mean that Litex imposes no constraints. Function domains and codomains, structure fields, and set-membership relations still undergo well-definedness checking; those constraints are simply written, as far as possible, where a mathematician would already write them. Litex also retains parameterized constructions such as `template`, because ordinary mathematics genuinely needs families of objects indexed by carriers, parameters, or hypotheses. Litex does not describe itself as a complete dependent type theory.

More importantly, Litex does not require the author to repeat the transport of these well-definedness conditions at every use. Once a function has a checked contract—its parameter domains, return set, and any call conditions—that contract becomes a reusable part of the function's mathematical interface. At a call, the verifier checks the actual arguments against the parameter domains, derives that the returned object belongs to the return set, and carries those facts through nested calls. The well-definedness obligation has not disappeared; what disappears from the source is the author's repeated transcription of its transport chain. This matches ordinary mathematical practice: after `f : A → B`, `g : B → C`, and `a ∈ A` have been established, one writes `g(f(a))` without restating `a ∈ A ⇒ f(a) ∈ B ⇒ g(f(a)) ∈ C`.

The same choice extends to mathematical structures such as groups. A structure still needs a carrier, and an operation still needs to say where its inputs and output live. The difference is that Lean's default interface presents those constraints first through types and functions, whereas Litex presents them first through sets, membership, and operations on sets.

Because these constraints remain expressed through objects and relations familiar to mathematicians, the value of a set-theoretic surface is not only shorter code. It also helps keep the formal statement directly reviewable.

<details>
<summary><strong>Specification Alignment in AI-Generated Mathematics</strong></summary>

A proof assistant can answer a precise formal question: does this proof establish the proposition that was actually encoded? It cannot, by kernel checking alone, answer a different question: is the encoded proposition exactly the mathematics its author intended to express? An AI-generated artifact may be internally valid while formalizing only a special case, changing a definition or domain, weakening the intended conclusion, or simply proving a different theorem under a plausible name. This is not a failure of logical soundness; it is a failure of alignment between mathematical intent and formal specification.

Stronger AI does not remove the need to compare mathematical intent with formal specification. The author or another responsible reviewer must still be able to read the formal statement and recognize the intended mathematics in it. Expert Lean users can perform such review, but Lean's type-theoretic abstractions, elaboration, type classes, library interfaces, and proof machinery can make the artifact difficult for the mathematician or domain expert who supplied the original claim to audit directly. If the people responsible for the mathematics cannot understand its formal expression, kernel acceptance can provide confidence in the wrong statement.

Litex's set-theoretic surface is intended to narrow this semantic gap. Sets, membership, domains, conditions, intermediate facts, and conclusions remain visible in a form closer to ordinary mathematical writing, while the language still gives them precise, machine-checkable meaning. Litex cannot automatically guarantee that an author or AI chose the intended definition or theorem, but it aims to make that choice inspectable by the people who understand the mathematics, rather than only by specialists in the proof assistant.

Readability matters after verification as well. A corpus that exposes its mathematical objects and facts can be compared, criticized, and reorganized by humans; recurring structures can become visible, and those structures may suggest better abstractions, new conjectures, or new mathematical viewpoints. If formal artifacts are readable only as implementation machinery, much of that opportunity for mathematical understanding and discovery is lost.

**The intended division of responsibility is therefore: AI may generate the formalization, the kernel checks the generated artifact against the formal proposition it states, and humans must still be able to verify that this proposition is what they meant. Litex treats that last step as a central language-design requirement.**

</details>

> **Position in the design space.** Set-theoretic presentation is not unique to Litex:
> [the Mizar Mathematical Library](https://wiki.mizar.org/library/) is based on Tarski–Grothendieck set theory;
> [Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) and
> [Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) expose dependent type-theoretic kernels to users; and
> [Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
> uses polymorphic higher-order logic.
>
> At the proposition level, Litex's user-facing language is broadly first-order in flavor. Facts begin with atomic relations between mathematical objects or calls to named predicates, and are organized with a deliberately restricted set of classical logical forms and quantifiers. “Restricted” matters here: Litex favors canonical fact shapes over arbitrary recursive combinations of formulas, and propositions and proofs cannot be passed around and composed arbitrarily as ordinary first-class values. This describes the proposition interface rather than claiming that the verifier is merely a general first-order prover: it also checks well-definedness and searches definitions, the current context, and supported builtin and inference rules for a justification.
>
> Against that background, Litex asks a more specific question about the user-facing object interface:
> can a small, membership-centered, set-theoretic surface cover substantive mathematics without first requiring users to manage type universes?

<a id="group-comparison"></a>

## From a Common Foundation to New Domains: Building a Mathematical Theory from the Ground Up

One important reason Litex chooses set theory is not merely to make sets, membership, and functions look like everyday mathematics. Set theory also provides different mathematical theories with a small, uniform starting point. Sets, functions, relations, and operations are already standard language in textbooks on analysis, abstract algebra, and linear algebra. Starting from them, a field's definitions and theorems can grow mainly along its own mathematical dependencies rather than first conforming to an existing encoding imposed by a large external library. We call this capacity **bootstrapping a mathematical theory**, or **self-contained theory construction**.

External libraries can supply reusable results and shorten the construction process, but they should not determine which mathematics can be expressed and developed. The group-definition example below is small enough to make this design choice concrete. The two fragments express the same familiar structure and the same uniqueness result for the identity, but provide different default interfaces for “what the carrier is,” “what a binary operation is,” and “how structural laws enter later proofs.”

<details>
<summary><strong>Full comparison: groups and uniqueness of the identity in Lean and Litex</strong></summary>

#### Lean: A Record over `Type` and Curried Functions

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

This Lean record begins with `Carrier : Type`: the group's elements, operations, and laws all depend on that carrier type. By the associativity convention for function types, the binary operation `Carrier → Carrier → Carrier` means `Carrier → (Carrier → Carrier)`, while structural laws become named, projectable fields such as `mul_assoc` and `one_mul`. This functional, type-theoretic interface offers strong abstraction and composition and supports precise reuse in large libraries. At the same time, authors interact with the host language's function constructions and the library's naming interface, and must know which theorem variant and equality direction they need. The uniqueness proof above explicitly writes `G.one_mul`.

#### Litex: Operations on a Set and Structural Facts Written Directly

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

Litex begins by binding a nonempty set `s` and models a group directly as a structure on that set. `mul fn(x, y s) s` directly denotes a binary operation that takes two elements of `s` and returns an element of `s`; the structural laws are written as ordinary mathematical facts inside `<=>:`. Users can begin with the mathematical materials—a set, an operation, an identity, inverses, and laws—and watch the group take shape one layer at a time. The uniqueness result is written directly as `identity = G.mul(G.one, identity) = G.one`, and the kernel searches for the corresponding instances of the identity laws and the needed equality directions. Litex does not forbid names: theorems worth citing over the long term and public interfaces can still be written as named `thm` definitions, but ordinary structural laws and local facts need not each enter a naming interface that authors must remember before those facts can be used.

This author-facing simplicity does not mean that structural laws are released automatically without bounds; the release rules remain explicit and checkable.

<details>
<summary><strong>Implementation note: the release boundary for struct facts</strong></summary>

A field path such as `G.mul` is well-defined from the struct carrier written in the definition; checking that path does not itself add the group laws to the context. The direct binder `G &Group<s>` above opens exactly one struct layer automatically. For a function result or a nested struct-valued field, authors write `by struct def expression`, which first verifies the expression's definition-owned struct membership and then releases only that layer. A later standalone fact `expression $in &Group<s>` remains opaque and cannot select a field view or release the laws by itself.

</details>

</details>

The Lean fragment itself shows that Lean can certainly define a group without relying on Mathlib's existing group interface. The real difference is not whether this is possible, but which experience is designed as the default path. For the authoring experience Litex seeks, set theory is especially suitable because sets, membership, functions, and relations form a cross-domain language close to everyday mathematics. Litex still depends on its own kernel, builtin rules, and standard library. Here, “building from the ground up” means that source dependencies in analysis, abstract algebra, or linear algebra should primarily reflect the theory's own mathematical structure, with external libraries serving as optional accelerators rather than boundaries on what can be expressed.

The group example is only a minimal demonstration of the principle. A stronger test is whether a small team can, in a relatively short time, build a readable, extensible, AI-usable formal interface for a domain not yet well covered by existing libraries, with explicit verification boundaries. Future libraries in geometry and other domains should test that claim with dated source, verifier results, `trust` boundaries, and reusable interfaces rather than treating it as already established.

If users do not first have to say “I want to invoke `one_mul`,” but can instead write “this is what the expression should equal,” then the source no longer centers on theorem names and proof commands. It centers on mathematical facts themselves.

<a id="fact-oriented"></a>
<a id="workflow"></a>

## 2. Fact-Oriented: Source Preserves *What Holds*

Fact orientation changes the division of labor between source code and kernel. User source code primarily preserves the objects and facts that should hold mathematically; the kernel is responsible for finding, checking, and explaining their local justification.

The set-inclusion interaction loop above already provides the smallest example: the user writes `x $in B` and `x $in c`, while the verification result records the known membership and subset relations supporting each fact. The same division of labor applies to analysis proofs involving definitions, quantifiers, witnesses, and inequality chains. The following comparison develops the full example that scalar multiplication preserves convergence.

<details>
<summary><strong>Full comparison: sequence convergence in Lean and Litex</strong></summary>

Lean is a widely used proof assistant and formal language that can rigorously check formal proofs written by humans and AI. Its default interaction begins from the final Goal—the current proposition to be proved. The user continually rewrites, decomposes, or closes the current Goal with tactics, from which the system constructs a proof term and submits it to the kernel for checking.

> **Lean tactics: The theorem first presents the final Goal → the user says how it should be rewritten, decomposed, or closed → the Infoview shows which Goals remain → tactics construct a proof term → the kernel checks that term.**

Consider the following example. First define convergence of a sequence, then prove from the definition that if the sequence `{s(n)}` converges to the real number `a`, the sequence `{c * s(n)}` converges to the real number `c * a`.

```lean
import Mathlib

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
    (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by
    exact div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngt
  calc
    |c * s n - c * a| = |c| * |s n - a| := by
      rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) :=
      mul_lt_mul_of_pos_left (hs n ngt) acpos
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm
```

The Lean proof above demonstrates a highly general, abstract, and compositional pattern—one that is an important source of Lean's expressive power. Its default direction of development, however, is not quite the same as ordinary mathematical writing, and beginners must also learn a substantial vocabulary of tactic keywords. Everyday mathematics more commonly proceeds in the following order:

1. Write down the objects, definitions, and conditions.
2. Recognize a familiar pattern.
3. Use a known fact, definition, or computation to write the next fact.
4. Let that fact become part of the context for later reasoning.

Litex makes this everyday mathematical workflow its default execution model. At the fact-oriented layer, the process can be summarized as:

> **Litex: The user states “what should hold” → the verifier searches for proof support → an accepted fact extends the current context.**

The corresponding Litex version reads more like ordinary mathematical expression:

```litex
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            abs(s(n) - a) < epsilon

prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}

thm converges_to_mul_const:
    ? forall s fn(n N) R, a, c R:
        $converges_to(s, a)
        =>:
            $converges_to(fn(n N) R {c * s(n)}, c * a)
    claim:
        ? forall epsilon R+:
            exist N0 N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)}
        abs(c) + 1 > 0
        epsilon / (abs(c) + 1) $in R+
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / (abs(c) + 1), K)}
        witness exist K N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, K)} from N0:
            forall n N:
                n >= N0
                =>:
                    abs(s(n) - a) < epsilon / (abs(c) + 1)
                    abs(c * s(n) - c * a) = abs(c * (s(n) - a)) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < (abs(c) + 1) * (epsilon / (abs(c) + 1)) = epsilon
                    abs(fn(k N) R {c * s(k)}(n) - c * a) < epsilon
            by def $is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)
    by def $converges_to(fn(n N) R {c * s(n)}, c * a)
```

</details>

<a id="goal-1"></a>

### Why Do Ordinary Facts Need Neither Names nor Tactics?

In the full convergence example above, `abs(c) + 1 > 0`, `epsilon / (abs(c) + 1) $in R+`, and the chain of inequalities are all unnamed. Nor does the user say line by line which tactic to call, which library theorem to use, or in which direction to rewrite. The user writes the mathematical facts they want to establish, and the kernel searches for rules and contextual support that can verify them.

> **The core human–machine division of labor in a fact-oriented system is: the user writes “what I want to prove”; Litex searches for “how this fact can be verified.”**

More concretely, the Litex kernel searches for proof support that matches the result and explains the verification path it finds. Lean's elaboration process instead follows the user's tactic commands to construct the corresponding proof term, the Infoview displays the transformed Goals, and the kernel checks that term.

This does not mean that Litex forbids naming. Classic theorems, standard-library interfaces, and dependencies the author wishes to make explicit can still be written as named Litex `thm` definitions and invoked with `release thm`, or selected with `by thm ... => fact`.

Ordinary facts need neither names nor explicit tactic calls because the Litex kernel searches for a verification path from the fact's predicate, argument shape, and current context. Common sources of verification include universal facts, whether builtin or user-provided, as well as known concrete facts and equality information. Litex also has more elaborate optimizations and strategies, but they do not change this core division of labor.

<details>
<summary><strong>Expanded: how the kernel searches for a verification path by fact shape</strong></summary>

#### 1. Match Fact Shapes with Builtin Rules

An atomic fact can be understood as a predicate plus arguments. Borrowing an analogy from natural language, the predicate is like a verb and the arguments are like the nouns the judgment is about. For example:

```text
a + b >= 0
```

Its relational predicate is `>=`, and its two arguments are `a + b` and `0`. The arguments themselves contain more structure that can be inspected: the outer shape on the left is addition, while the right side is zero. The kernel can use this shape to narrow the candidates without first knowing a name for the fact.

For example:

```litex
have a R = 1
have b R = 2

a + b >= 0
```

In this local context, the user's submitted target is the final line, `a + b >= 0`. The kernel sees the predicate `>=`, then observes that the left argument has addition as its outer shape and the right argument is `0`, so it tries the corresponding builtin nonnegativity rule. Litex has the following builtin rule:

```text
forall x, y R:
    x >= 0
    y >= 0
    =>:
        x + y >= 0
```

Matching the target conclusion against the rule conclusion yields `x := a` and `y := b`. The kernel then checks the instantiated premises `a $in R`, `a >= 0` (`1 >= 0`), `b $in R`, and `b >= 0` (`2 >= 0`), and therefore accepts the target fact.

#### 2. Match with User-Provided Universal Facts

Candidates do not come only from builtin rules. Ordinary `forall` facts that the user has already proved or explicitly assumed can also participate in automatic matching:

```litex
abstract_prop p(x)

trust forall a R:
    $p(a)

$p(1)
```

For the target `$p(1)`, the kernel first uses the predicate `p` to find a universal fact whose conclusion has the shape `$p(a)`, then matches the argument `a` to `1`. This instantiation also requires `1 $in R`; because that condition passes checking, the kernel can use the universal fact to verify `$p(1)`.

`abstract_prop` is Litex syntax for declaring an abstract predicate without supplying a definition. A `trust` statement produces a warning and means that the fact is accepted without verification. An artifact containing `trust` is not fully checkable; `trust` can mark an external assumption or proof debt that has not yet been eliminated.

#### 3. Match with Concrete Facts and Known Equalities

A third common source is not a universal rule but an already known concrete fact:

```litex
abstract_prop q(x)

forall a R:
    $q(a)
    a = 1
    =>:
        $q(1)
```

To verify `$q(1)`, the kernel finds the known fact `$q(a)` with the same predicate. The two arguments are not textually identical, but the context also knows `a = 1`, so they match under the current equality information. The kernel can therefore transport `$q(a)` to `$q(1)`.

</details>

### Summary: Put *What to Prove* in the Source and Leave the Search for *How* to the Kernel

This writing style is closer to everyday mathematical prose. Mathematicians do not usually identify explicitly, at every step, the theorem, equality, or definition they are about to use. They write the conclusion they want, and readers understand why it follows from the context and known facts.

<details>
<summary><strong>A personal analogy: declarative and imperative styles</strong></summary>

An imperfect programming analogy can help here. Declarative source tends to emphasize *what should be produced*, while imperative source tends to emphasize *how to produce it*. Litex's fact-oriented style is closer to the former: users state *what is to be proved*, and the kernel searches for *how to prove it*. Because Litex automatically searches both for the conditions that make an expression well-defined and for support that justifies a stated fact, authors usually do not need to name ordinary facts first and then cite them explicitly with `by ...` at later sites. This reduces explicit dependency threading and helps the language retain a smaller, more uniform surface syntax. Lean itself is a functional language, but its tactic workflow can feel more imperative at the interaction level because the source describes a sequence of transformations to the current proof state. This is an analogy about interaction style, not a strict classification of programming languages.

</details>

> **Position in the design space.** Searching for local proof support is not unique to Litex:
> [Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/),
> [Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html),
> and [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) provide local automation through explicit tactics or
> proof methods; [Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf)
> has empty justification;
> [ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM) can attempt to prove a theorem event without hints; and
> [Naproche](https://naproche.github.io/) uses automated theorem provers
> to check proof steps written in controlled natural language. Litex tests a more specific hypothesis: can ordinary
> mathematical statements themselves trigger local justification, with verification bounded by the current context and
> supported rules, and with an accepted fact written back into the context and its verification source displayed?

<a id="goal-3"></a>
<a id="bottom-up"></a>
<a id="two-directions"></a>

## 3. Bottom-Up: Let Verified Facts Continue to Grow

Mathematical facts are the basic units of Litex source. Within a proof, those facts do not stand alone: each verified fact extends the current context and becomes a known condition that later statements can use. As new facts accumulate, the proof flow moves forward from known conditions toward the conclusion. This is what “bottom-up” means here.

By design, Litex supports **declarative proof writing whose default flow is mostly forward reasoning**. The default unit of reasoning is the next mathematical fact in the current context, not an active Goal that every line must immediately advance. As long as a statement is in the current scope, is well-defined, and has sufficient support in the existing context, the kernel can accept it, store it, apply currently relevant inference rules, and pass the enriched context to later statements. Several mathematical branches can grow separately before later statements bring them together.

Lean's usual interactive theorem proving is goal-directed, with a typical direction that is backward and top-down. The final theorem first fixes the final Goal. Local terms and tactic commands are elaborated under that expectation, progressively decomposing the Goal or reducing it backward to simpler subgoals until Lean can assemble a complete proof term.

The default questions can be summarized as follows: Lean asks, “How can I simplify the current Goal until it reduces to known conditions?” Litex asks, “Given the known conditions, what fact can I derive next?”

> Think of writing a proof as building with LEGO bricks. At the start, we have a collection of available pieces and know what the final model should be. A typical Lean tactic workflow is like beginning with the finished model and disassembling it backward until the requirements can be met by the pieces at hand. A typical Litex workflow starts from the available pieces and builds forward, allowing one verified local result after another to converge on the final model. This analogy describes only the default direction of development. It does not imply that Litex has a weaker verification standard, nor that either system can work in only one direction.

### Two Directions for Developing the Same Proof: Top-Down and Bottom-Up

#### Example 1: Algebraic Rewriting

This local rewriting example shows how the same equality can be developed in two directions. In Lean, the user begins from the Goal and uses each `rw` command to specify which fact should be invoked next, in which direction it should match, and what it should replace:

```lean
-- Using facts from the local context.
example (a b c d g f : ℝ) (h : a * b = c * d) (h' : g = f) :
    a * (b * g) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

The corresponding Litex version reverses Lean's four Goal-directed rewrites into a single equality chain. The chain begins at the right side of the Goal, `c * (d * f)`, writes each intermediate result, and ends at the left side, `a * (b * g)`:

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

These four equalities correspond exactly, in reverse order, to Lean's four `rw` commands. The Lean code tells the system which fact to invoke next and in which direction to rewrite the Goal. The Litex code tells the system what the important intermediate results should be if the reasoning succeeds. The kernel then searches the current context, equality matching, and structural rules for grounds that justify each adjacent equality.

For humans and AI, the bottom-up workflow is also valuable because progress can accumulate. A sequence of separately submitted and accepted statements can remain as a verified prefix, while the next `unknown` identifies the current repair point. Accepted parts of an unfinished attempt can be inspected, reused, and continued. A composite statement whose internal conclusion fails, however, is not partially written into the environment.

This convenience has an explicit trust cost. Litex places hundreds of common proof patterns into builtin and infer rules, moving some work that would otherwise live in user proof scripts into a larger trusted computing base. The proof obligation has not disappeared; it has moved. Recording verification routes and handing covered paths to the smaller Lean kernel for rechecking is therefore an essential next link in the design.

<details>
<summary><strong>Position in the design space: forward proof is not unique to Litex</strong></summary>

Mizar and Isar already support forward, declarative proof text; ACL2 accumulates a reusable theorem database; and Naproche checks mathematical statements incrementally. “Growing bottom-up” is therefore not by itself Litex's differentiating claim. Litex tests a particular combination: submitting an ordinary fact triggers verification and, on success, extends the context; local justification starts without a separate proof-method invocation; and the author writes explicit proof structure only when ordinary automatic verification is insufficient.

</details>

For this larger verification mechanism to receive independent rechecking, Litex must hand its recorded verification paths to the smaller Lean kernel.

<a id="compatibility"></a>

## 4. Lean-Compatible: Independent Rechecking for Covered Paths

Litex is first an independently usable formal language. It has its own syntax, runtime, and kernel. Even when a Litex mathematical document is not compiled to Lean, Litex can directly check its well-definedness and facts and provide local proof feedback. “A mathematical front-end language for Lean” therefore means that the Litex-to-Lean compiler translates the verification paths it currently supports into Lean proof terms, expanding its coverage incrementally to connect with the Lean ecosystem. *I hope Litex's development can provide the Lean community with new formal mathematical content and interface experience, while Lean's kernel and Mathlib ecosystem can in turn strengthen Litex. The relationship is complementary, not competitive.*

Fact-first, small-step verification lets humans and AI focus on mathematical objects, conditions, intermediate facts, and conclusions while receiving fast, local, and traceable feedback from the Litex kernel. By comparison, mechanisms such as elaboration, type classes, namespaces, and tactic calls are important sources of Lean's expressiveness and compositionality as a general-purpose programming language.

*The compiler gives this relationship a second role: an important independent safeguard for Litex's rigor.* The Rust source under Litex's `src/` directory alone currently contains close to 200,000 lines, and that surface continues to grow with hundreds of builtin and infer rules and new capabilities. Auditing such a large trusted implementation is naturally harder than auditing Lean's much smaller kernel. When a Litex verification path can be compiled in full into a Lean proof and accepted by the Lean kernel, it supplies strong, independent correctness evidence for that covered path and substantially reduces reliance on Litex's own large implementation as the sole basis of trust.

_This remains a goal that Litex is implementing and testing, not a capability already achieved comprehensively by the current beta. The Litex-to-Lean compiler currently covers only some verification paths. Its basic design and framework are in place, but many details still need work. Community feedback and contributions are welcome._

<details>
<summary><strong>How the Litex-to-Lean Compiler Works</strong></summary>

The two roles of ecosystem reuse and independent rechecking point to a natural technical route. Litex is based on set theory, and Lean's Mathlib includes substantial support for set-theoretic mathematics. Litex's verification system saves users from writing many proof-construction steps themselves, but the verifier records the route it used. In principle, each supported and recorded verification step can be represented by an appropriate Lean theorem or proof construction and assembled into a proof term. That is why a Litex-to-Lean compiler is a natural architectural goal.

Making that route concrete requires a mapping to Lean and Mathlib. For verification, the compiler maps each supported Litex verification path to the corresponding Lean proof construction. For mathematical objects, it maps each Litex object to a Lean representation—not by translating it directly, but by using designed wrappers as an intermediary. This mapping is feasible, but it takes time to develop and verify. The intermediary code lives at https://github.com/litexlang/golitex/blob/main/lean/Litex/Core.lean and remains under active development.

The executable [Litex-to-Lean-to-Mathlib pipeline](../showcases/litex_to_lean_mathlib_pipeline/README.md) shows the concrete Rust call spine, the recursive `StmtResult` evidence retained at the kernel boundary, the generated Lean proof, a separate external adapter, and its downstream Mathlib consumer. The Blueprint keeps the stable architecture; that showcase owns the implementation-level source map and runnable gates.

A small numerical theorem illustrates both the evidence-preserving mapping and
the desired ecosystem interface. Consider this checked Litex theorem:

```litex
thm litex_real_add_comm:
    ? forall a, b R:
        a + b = b + a
```

This example distinguishes two Lean interfaces. The first is the canonical compiler theorem, which keeps the Litex
classification and verification evidence:

```text
∀ {α β : Type} (a : α) (ha : Litex.In a Litex.R)
  (b : β) (hb : Litex.In b Litex.R),
  Litex.Same
    ((Litex.In.rep a ha : ℝ) + (Litex.In.rep b hb : ℝ))
    ((Litex.In.rep b hb : ℝ) + (Litex.In.rep a ha : ℝ))
```

The compiler stops at that source-owned declaration. It does not additionally
invent the ordinary Lean corollary

```text
theorem litex_real_add_comm (a b : ℝ) : a + b = b + a
```

because no such declaration exists in the `.lit` file. This
declaration-preserving boundary keeps generated Lean auditable: theorem names,
statements, and proof routes all trace back to source-owned facts.

If an ordinary Mathlib interface is useful, an external AI or human writes it
in a separate, non-generated Lean module. That adapter may import and inspect
the generated module, but it owns the new statement and its Lean proof. The
compiler does not hide API design or fresh target-language mathematics inside
translation.

**Interoperability therefore has two explicit artifacts: ToLean supplies the
kernel-checkable translation of the Litex source, while an external adapter
supplies any additional Lean/Mathlib-facing API. Lean users can import the
adapter without confusing it with compiler output.**

This example also exposes the compiler's two underlying design problems. The first is theoretical: how to represent Litex mathematics in Lean and Mathlib. The same mathematical object or statement can often be expressed by several Lean formulations with the same mathematical meaning, but the choice has long-term consequences for whether generated code can reuse Mathlib naturally, how later Litex features can be extended, and how well the Litex and Lean ecosystems can work together. Foundational concepts such as functions, sets, membership, and well-definedness therefore need a consistent and sustainable representation—not merely one that makes today's examples pass.

The second problem is practical: how to turn the information produced by successful Litex kernel execution into Lean proofs. Litex verification decomposes a goal into smaller subgoals along a search tree; a successful branch must return structured information from the leaves to the root, recording the rules, facts, mathematical objects, subproofs, and well-definedness results involved. Declarations, objects, facts, and scope changes produced during statement execution must be preserved as well, allowing the compiler to replay the verification route Litex already found deterministically instead of reconstructing a proof from display text or asking Lean to search for another one.

</details>

The connection between Litex and Lean is therefore not a matter of one replacing the other. Litex can provide a mathematics-facing authoring interface, while Lean provides small-kernel rechecking and ecosystem reuse. For the paths already covered by the compiler, these two layers can form one verifiable, reviewable, and reusable workflow.

<a id="ecosystem-role"></a>

## From Language to Ecosystem: The Role Litex Aims to Play

**Litex is designed for humans and AI. It serves both as a front end for readable reasoning and as a production layer for trustworthy reasoning data, connecting to the existing formal-mathematics ecosystem through Lean and Mathlib. It aims to make formal languages not only tools for mathematicians and proof-assistant experts, but also tools that AI, engineers, and practitioners in other fields can use to check, organize, and advance trustworthy reasoning.**

These three roles correspond to the following concrete outputs:

| Ecosystem role | Outputs Litex aims to produce |
| --- | --- |
| Front end for readable reasoning | Mathematical objects, conditions, intermediate facts, and conclusions that people can inspect directly |
| Production layer for trustworthy reasoning data | Machine-checked facts and verification sources, explicit stopping boundaries, and explicitly marked uses of `trust` and other trust boundaries |
| Connection to the existing ecosystem | Lean proof terms for currently supported source routes, plus explicitly separate AI- or human-authored adapters for additional Lean/Mathlib interfaces |

“Trustworthy reasoning data” does not mean that every Litex output already has the same trust guarantees as a mature proof assistant. It first means that the data carries machine-checking results, verification sources, and explicit boundaries. Litex's own builtin and infer rules, uses of `trust`, and implementation remain part of the surface that must be audited. Only when a verification route is compiled in full and accepted by the Lean kernel does that covered route gain an additional, smaller, and relatively independent kernel check. Compiler coverage and the separate adapter ecosystem are still expanding.

The amount of Litex code and the size of its datasets are therefore intermediate measures. What matters is whether people can understand the resulting artifacts, machines can check them, later reasoning can reuse them, and—within the currently supported surface—they can enter an existing formal-mathematics toolchain. Only through those outcomes could Litex grow from a language experiment into reasoning infrastructure shared by mathematics, AI, engineering, and other fields.

<a id="conclusions"></a>

## Conclusion

Litex aims to make writing and verifying formal mathematics closer to everyday mathematical thought. By offering syntax and an interaction contract closer to ordinary mathematical writing, Litex seeks to lower the barrier to formal authorship and review, make mathematical text executable, and support deeper mathematical understanding and discovery.

Litex's four design choices serve one division of labor. Set theory keeps mathematical objects and constraints readable. Fact orientation lets source preserve *what holds*. Bottom-up proof flow lets verified facts accumulate. Lean compatibility provides independent rechecking and an ecosystem path for verification routes already covered by the compiler. Litex is not trying to replace Lean. It tests a complementary hypothesis: whether a smaller front end closer to ordinary mathematics can let students, domain researchers, and AI engineers produce, review, and repair checked mathematics at lower cost.

**Litex's success will not be measured by how much Litex code is written, but by whether it can turn readable reasoning into useful results that interoperate with existing formal-language systems and genuinely serve mathematics, AI, engineering, and other fields.**

This means evaluating outcomes rather than output volume alone: can people read and audit the mathematical intent directly; can humans and AI use verification support and stopping boundaries to continue the work; can checked facts be reused across files, projects, and datasets; can currently supported verification routes enter Lean and Mathlib for independent rechecking; and are these artifacts actually adopted by tasks in mathematics, AI, engineering, or other fields? Code volume, theorem counts, and dataset size can track progress, but none of them alone establishes that these goals have been achieved.

If this direction works, it can first lower the barrier to formal authorship and review, then let readable mathematical text become a checked and reusable artifact, and eventually help humans and AI understand relationships among mathematical objects, definitions, theorems, and proofs more systematically. Deeper mathematical understanding and discovery are possible long-term outcomes of that process, not conclusions already secured by the language design itself.

### Related Links

1. To try examples directly and inspect Litex's output and knowledge graphs, visit [litexlang.com](https://litexlang.com).

2. For the kernel implementation, see the [golitex repository](https://github.com/litexlang/golitex).

Note: At the current research stage, Litex develops its research program and explains its goals in public. The repository therefore contains checked results, experiments, and unfinished work side by side. *Publicly visible does not mean claimed complete.* Each capability should be judged by its current tests, dated status notes, trusted boundary, and known limitations.
