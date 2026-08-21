# Litex: A Formal Language Where Mathematics Verifies Itself

Created and maintained by Jiachen Shen.

Website: https://litexlang.com/doc/Litex_Blueprint

Chinese version: https://litexlang.com/doc/Litex中文蓝图

> **Litex is an experimental hobby project and remains in beta. Expect edge cases.**

## Table of Contents

- [Litex Blueprint Overview](#overview)
- [Background: The AI Era Needs Formal Languages](#background)
- [1. Based on Set Theory: Let Set-Theoretic Knowledge Look Like Set Theory](#set-theory)
  - [Two Ways to Define a Group: Building a Mathematical Theory from the Ground Up](#group-comparison)
- [2. Fact-Oriented: Starting from the Everyday Mathematical Workflow—Definitions, Theorems, and Proofs](#fact-oriented)
- [3. Building Proof Flow Bottom-Up](#bottom-up)
  - [Two Directions for Developing the Same Proof: Top-Down and Bottom-Up](#two-directions)
- [4. Lean-Compatible: A Path to Lean's Trusted Ecosystem](#compatibility)
- [Conclusion](#conclusions)

<a id="overview"></a>

## Litex Blueprint Overview

*Litex is a set-theory-based, fact-oriented, bottom-up, Lean-compatible formal language.*

1. Based on set theory: Litex is founded on ZFC set theory and organizes mathematical objects uniformly through sets and membership. The same object can belong to multiple sets, and objects, facts, and mathematical statements are separate. By comparison, Lean's `Set α` first depends on the more abstract carrier type `α : Type*`, while mathematical objects and mathematical facts are themselves types. Type theory offers stronger generality and compositionality. Litex instead provides a more direct surface interface for set theory and the common mathematical knowledge built on it.
2. Fact-oriented: Litex source code primarily states *what mathematical facts should hold*. Based on each fact's predicate and arguments, the kernel looks for a verification route among builtin rules, previously proved facts, and equality matching. It also checks that objects and expressions are well-defined before accepting a fact. By comparison, typical Lean tactic source code primarily states *how to handle the next Goal*, while the Infoview shows which Goals remain after each operation.
3. Building proof flow bottom-up: A mathematical proof can start from known conditions, derive new facts, and eventually converge on the conclusion. It can also start from the final Goal and reduce it backward to known conditions. Litex defaults to the former workflow, in which the context grows forward with verified facts; common Lean tactic interactions usually adopt the latter. Neither system excludes the other direction from what it can express.
4. Lean-compatible: The goal of the Litex-to-Lean compiler is to translate verification paths already found by the Litex kernel into Lean proof terms, which the Lean kernel can then check independently. The current compiler covers only some verification paths. “Every Litex source file can be compiled to Lean” is an unfinished direction, not a capability already delivered by the beta release.

The hope is that using Litex can feel like doing informal mathematics: users can keep their attention on mathematical objects, conditions, intermediate facts, and conclusions without first having to confront abstract mathematical theories, unfamiliar formal syntax, or vast external libraries. Litex acts as their copilot, providing fast, local, and traceable verification feedback. *The hope is that Litex will make it easier for non-specialists across many fields to enter the world of formal mathematics.*

I will first provide the background, then address the four key terms in this summary in turn: **based on set theory, fact-oriented, building proof flow bottom-up, and Lean-compatible**. I hope this highly condensed, subjective, and exploratory blueprint will give readers an overall impression of Litex's design philosophy and goals, allowing them to follow the author's line of thought and “reinvent Litex” along the way.

<a id="background"></a>

## Background: The AI Era Needs Formal Languages

From Arabic numerals, to Leibniz's notation for calculus, to TeX and LaTeX, important new systems of mathematical notation have often done more than shorten writing. They have also quietly changed how people see problems, organize reasoning, and explore new directions. Formal languages are a new stage in mathematical notation: they let humans write mathematics more precisely and let machines check that writing rigorously. Today, AI is making the generation of candidate mathematical proofs broader and more scalable. As proofs cease to be only texts written by hand by a small number of people, the central bottleneck will gradually move from “can we generate an argument that looks plausible?” to “can we reliably check, reuse, and accumulate it?”

*Yet mainstream formal languages and proof assistants are still designed primarily for expert researchers. Their syntax, interaction models, and workflows often differ substantially from everyday mathematical writing. Beginners must spend considerable time learning these differences before they can express the mathematics they care about. Outside mathematics, AI safety researchers, software engineers, physicists, economists, statisticians, and others may also need formal languages to express mathematics, but they may have neither the time nor the interest to learn the internals of sophisticated proof assistants.*

Litex aims to bring this technology closer to ordinary learners and users of mathematics. Its ideal is: **whatever mathematics you want to express, you should be able to express in a formal language.** For example, someone who already knows secondary-school mathematics should be able to learn quickly how to express that mathematics in Litex without first becoming an expert in proof assistants.

> This is a design target, not a claim about current language or library coverage.

To understand why this goal calls for a different language design, first consider the relationship between formal proof and the workflows common in everyday mathematics.

> **Note.** Lean remains the main comparison throughout this blueprint because it makes the
> difference between Goal-first and fact-first workflows especially concrete. References to Mizar,
> Isabelle/Isar, Rocq, ACL2, and Naproche locate Litex within the existing design space. Litex was
> designed independently and was not derived from these systems. They are cited to identify nearby
> ideas and the differences that ultimately emerged, not to claim direct intellectual influence.

<details>
<summary><strong>Basic terms before reading: formal language, Goal, tactic, and kernel</strong></summary>

*If you have not used Lean or another proof assistant, you may want to read this subsection first. Skipping it will not affect the mathematical examples that follow.*

- **Formal language**: A language whose syntax and meaning are governed by explicit rules and can therefore be parsed and checked by a machine. “Formal” means that expressions have precise semantics; it does not mean that the prose sounds formal. A formal language also need not be a general-purpose programming language.
- **Proof assistant**: Software that helps users express proofs, provides interactive feedback, and checks proofs mechanically. Lean is a proof assistant with general-purpose programming capabilities.
- **Goal and Infoview**: A Goal is a proposition currently waiting to be proved. The Infoview is the window in the Lean editor that displays the current Goal, local variables, and known hypotheses.
- **Context**: The variables, definitions, assumptions, and verified facts available in the current scope. Adding a new fact extends the context so that later reasoning can use it.
- **Tactic**: A command that operates on the current Goal—for example, introducing variables, rewriting by an equality, or splitting one Goal into several subgoals. A tactic describes *what to do next in the proof*; it is not itself the final proof object accepted by the kernel.
- **Proof term and elaboration**: A proof term is the complete proof object a machine can check. Elaboration is the process by which the system fills in information omitted from the source and turns user code into a complete proof term.
- **Kernel**: In Lean, the kernel is the trusted core that checks proof terms according to foundational rules. Tactics may be complex, but their results must still pass kernel checking; the kernel generally does not choose high-level proof steps for the user.
- **Kernel/verifier**: A broad term for the part of a system responsible for checking. The Litex kernel not only checks that objects are well-defined but also searches builtin rules and the current context for grounds that verify a fact. It therefore cannot be identified directly with Lean's kernel. Litex's trusted boundary—the part on whose correctness the system relies and which must be trusted—is correspondingly larger.

The two workflows can first be simplified as follows:

```text
Lean: proposition → Goal → tactics and elaboration → proof term → kernel check
Litex: objects and facts → kernel checks and searches for justification → verified facts extend the context
```

</details>

<a id="set-theory"></a>
<a id="goal-2"></a>

## 1. Based on Set Theory: Let Set-Theoretic Knowledge Look Like Set Theory

Litex organizes its surface language directly around sets, membership, and relations between sets. When the problem itself is set-theoretic, users can write sets, subsets, and intersections directly, without first introducing a type that carries those sets.

The following Litex code states that intersection is monotone with respect to inclusion:

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

This is not a proof hole left to be filled; it is a complete fact submitted to the kernel for checking. Its ordinary mathematical reading is: take any member `x` of `intersect(s, u)`. Then `x` belongs to both `s` and `u`. Since `s $subset t`, it also belongs to `t`, and therefore to `intersect(t, u)`. The user states the mathematical result that should follow; the kernel searches for a verification path by unfolding intersection membership, transporting membership along a subset relation, and reassembling membership in the intersection on the right.

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

Litex chooses a different task boundary. Because it takes set-theoretic objects and membership as its foundational surface, the language and kernel can provide specialized syntax and verification paths for high-frequency set-theoretic knowledge about sets, membership, subsets, intersections, and unions. For this task, the user need only declare three sets and the expected inclusion, so the code is closer to everyday set-theoretic writing and is visibly shorter.

The difference should not be reduced to “short code is necessarily stronger than long code.” Lean can prove the same proposition with a shorter proof term or with automation. The version above deliberately preserves the pedagogical route from *Mathematics in Lean*: unfold the definitions, decompose membership in the intersection, and then assemble it again. The real comparison concerns the default interface. Lean first gives a set a type-theoretic carrier, after which the user or a tactic constructs a proof. Litex instead makes common set-theoretic relations into mathematical facts the language can recognize and check directly.

This set-theoretic surface does not mean that Litex imposes no constraints. Function domains and codomains, structure fields, and set-membership relations still undergo well-definedness checking; those constraints are simply written, as far as possible, where a mathematician would already write them. Litex also retains parameterized constructions such as `template`, because ordinary mathematics genuinely needs families of objects indexed by carriers, parameters, or hypotheses. Litex does not describe itself as a complete dependent type theory.

The same choice extends to mathematical structures such as groups. A structure still needs a carrier, and an operation still needs to say where its inputs and output live. The difference is whether those constraints are presented first as types and functions or first as sets, membership, and operations on sets.

<details>
<summary><strong>Further reading: how Litex helps ensure AI-generated mathematics says what we mean</strong></summary>

A proof assistant can answer a precise formal question: does this proof establish the proposition that was actually encoded? It cannot, by kernel checking alone, answer a different question: is the encoded proposition exactly the mathematics its author intended to express? An AI-generated artifact may be internally valid while formalizing only a special case, changing a definition or domain, weakening the intended conclusion, or simply proving a different theorem under a plausible name. This is not a failure of logical soundness; it is a failure of alignment between mathematical intent and formal specification.

Stronger AI does not remove the need for this comparison. The author or another responsible reviewer must still be able to read the formal statement and recognize the intended mathematics in it. Expert Lean users can perform such review, but Lean's type-theoretic abstractions, elaboration, type classes, library interfaces, and proof machinery can make the artifact difficult for the mathematician or domain expert who supplied the original claim to audit directly. If the people responsible for the mathematics cannot understand its formal expression, kernel acceptance can provide confidence in the wrong statement.

Litex's set-theoretic surface is intended to narrow this semantic gap. Sets, membership, domains, conditions, intermediate facts, and conclusions remain visible in a form closer to ordinary mathematical writing, while the language still gives them precise, machine-checkable meaning. Litex cannot automatically guarantee that an author or AI chose the intended definition or theorem, but it aims to make that choice inspectable by the people who understand the mathematics, rather than only by specialists in the proof assistant.

Readability matters after verification as well. A corpus that exposes its mathematical objects and facts can be compared, criticized, and reorganized by humans; recurring structures can become visible, and those structures may suggest better abstractions, new conjectures, or new mathematical viewpoints. If formal artifacts are readable only as implementation machinery, much of that opportunity for mathematical understanding and discovery is lost.

**The intended division of responsibility is therefore: AI may generate the formalization, the kernel checks the generated artifact against the formal proposition it states, and humans must still be able to verify that this proposition is what they meant. Litex treats that last step as a central language-design requirement.**

</details>

> **Position in the design space.** Set-theoretic presentation is not unique to Litex:
> [the Mizar Mathematical Library](https://wiki.mizar.org/library/) is based on Tarski–Grothendieck set theory;
> [Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) and
> [Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) expose dependent type-theoretic kernels to users; and
> [Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
> uses polymorphic higher-order logic. Litex asks a more specific question about the user-facing object interface:
> can a small, membership-centered, set-theoretic surface cover substantive mathematics without first requiring users to manage type universes?

<a id="group-comparison"></a>

### Two Ways to Define a Group: Building a Mathematical Theory from the Ground Up

One important reason Litex chooses set theory is not merely to make sets, membership, and functions look like everyday mathematics. Set theory also provides different mathematical theories with a small, uniform starting point. Sets, functions, relations, and operations are the familiar language in which textbooks organize analysis, abstract algebra, and linear algebra. Starting from them, a field's definitions and theorems can grow mainly along its own mathematical dependencies rather than first conforming to an existing encoding imposed by a large external library. We call this capacity **bootstrapping a mathematical theory**, or **self-contained theory construction**.

External libraries can supply reusable results and shorten the construction process, but they should not determine which mathematics can be expressed and developed. A group is small enough to make this design choice concrete. The following two fragments express the same familiar structure and the same uniqueness result for the identity, but provide different default interfaces for “what the carrier is,” “what a binary operation is,” and “how structural laws enter later proofs.”

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

Litex starts from `s nonempty_set` and models a group directly as a structure on the nonempty set `s`. `mul fn(x, y s) s` directly denotes a binary operation that takes two elements of `s` and returns an element of `s`; the structural laws are written as ordinary mathematical facts inside `<=>:`. Users can begin with the mathematical materials—a set, an operation, an identity, inverses, and laws—and watch the group take shape one layer at a time. The uniqueness result is written directly as `identity = G.mul(G.one, identity) = G.one`, and the kernel searches for the corresponding instances of the identity laws and the needed equality directions. Litex does not forbid names: theorems worth citing over the long term and public interfaces can still be written as named `thm` declarations, but ordinary structural laws and local facts need not each enter a naming interface that authors must remember before those facts can be used.

The release of those structural facts is nevertheless bounded and explicit. A
field path such as `G.mul` is well-defined from the struct carrier written in
the declaration; checking that path does not itself add the group laws to the
context. The direct binder `G &Group<s>` above opens exactly one struct layer
automatically. For a function result or a nested struct-valued field, authors
write `by struct def expression`, which first verifies the expression's
declaration-owned struct membership and then releases only that layer. A later
standalone fact `expression $in &Group<s>` remains opaque and cannot select a
field view or release the laws by itself.

The Lean fragment itself shows that Lean can certainly define a group without relying on Mathlib's existing group interface. The real difference is not whether this is possible, but which experience is designed as the default path. For the authoring experience Litex seeks, set theory is especially suitable because sets, membership, functions, and relations form a cross-domain language close to everyday mathematics. Litex still depends on its own kernel, builtin rules, and standard library. Here, “building from the ground up” means that source dependencies in analysis, abstract algebra, or linear algebra should primarily reflect the theory's own mathematical structure, with external libraries serving as optional accelerators rather than boundaries on what can be expressed.

This example naturally leads into the next section. If users do not first have to say “I want to invoke `one_mul`,” but can instead write “this is what the expression should equal,” then the source no longer centers on theorem names and proof commands. It centers on mathematical facts themselves.

<a id="fact-oriented"></a>
<a id="workflow"></a>

## 2. Fact-Oriented: Starting from the Everyday Mathematical Workflow—Definitions, Theorems, and Proofs

This section uses definitions, theorems, and proofs to explain concretely what a fact-oriented design changes. User source code primarily preserves the objects and facts that should hold mathematically; the kernel is responsible for finding, checking, and explaining their local justification.

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

Litex makes this everyday mathematical workflow its default execution model. The entire process can be summarized as:

> **Litex: The user states “what should hold” → the verifier searches for proof support → the output explains why and how the statement was verified → the verified fact extends the current context → the proof grows bottom-up.**

For a beginner, the Litex version of the same sequence problem reads more like ordinary mathematical expression:

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

<a id="goal-1"></a>

### Why Do Ordinary Facts Need Neither Names nor Tactics?

In the convergence example, `abs(c) + 1 > 0`, `epsilon / (abs(c) + 1) $in R+`, and the chain of inequalities are all unnamed. Nor does the user say line by line which tactic to call, which library theorem to use, or in which direction to rewrite. The user writes the mathematical facts they want to establish, and the kernel searches for rules and contextual support that can verify them.

> **The core human–machine division of labor in a fact-oriented system is: the user writes “what I want to prove”; Litex searches for “how this fact can be verified.”**

**Litex users primarily state the *what*: “what should hold.” Lean tactic users primarily state the *how*: “how should the current Goal be handled?”** The Litex kernel searches for proof support that matches the result and explains the verification path it finds. Lean's elaboration process follows the user's tactic commands to construct the corresponding proof term, the Infoview displays the transformed Goals, and the kernel checks that term.

Consider the instructions for building with LEGO bricks. An instruction booklet gives both the action to perform at each step and a picture of the result after that step. Lean source is analogous to writing the sequence of actions. Litex source is analogous to writing only the desired intermediate results and letting the kernel find the actions.

This does not mean that Litex forbids naming. Classic theorems, standard-library interfaces, and dependencies the author wishes to make explicit can still be written as named Litex `thm` declarations and invoked with `by thm`.

The following examples show how Litex verifies submitted facts without requiring names or tactics. In one sentence: a fact is verified either by a universal fact—builtin or user-provided—or by known concrete facts together with equality information. The kernel uses the predicate and argument shape of a fact to search for an acceptable verification path. Litex also has more elaborate optimizations and strategies, but they do not change this core division of labor.

<details>
<summary><strong>Expanded: how the kernel searches for a verification path by fact shape</strong></summary>

#### 1. Match Fact Shapes with Builtin Rules

An atomic fact can be understood as a predicate plus arguments. Borrowing an analogy from natural language, the predicate is like a verb and the arguments are like the nouns the judgment is about. For example:

```text
a + b >= 0
```

Its relational predicate is `>=`, and its two arguments are `a + b` and `0`. The arguments themselves contain more structure that can be inspected: the outer shape on the left is addition, while the right side is zero. The kernel can use this shape to narrow the candidates without first knowing a name for the fact.

Consider the main example for this subsection:

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

`abstract_prop` is Litex syntax for declaring an abstract predicate without supplying a definition. A `trust` declaration produces a warning and means that the fact is accepted without verification. Use `trust` carefully; it is normally reserved for tests or isolated examples.

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

#### Summary: Litex Source States *What* to Prove and Leaves the Search for *How* to the Kernel

This writing style is closer to everyday mathematical prose. Mathematicians do not usually identify explicitly, at every step, the theorem, equality, or definition they are about to use. They write the conclusion they want, and readers understand why it follows from the context and known facts.

> **A personal perspective.** One way I think about this distinction is through functional and procedural programming. Functional programming—as seen in languages or ecosystems such as JavaScript, Lisp, and Lean—often leans toward the declarative: source code says more about *what* should be produced. Procedural programming—as seen in languages such as C/C++, Go, and Rust—often leans toward the imperative: source code says more about *how* to produce it. Litex's style is closer to the declarative side: the user states *what is to be proved*, and the kernel searches for *how to prove it*. Although Lean is a functional language, writing mathematics with tactics can feel more procedural: the source tells the system *how to construct the proof*.

> **Position in the design space.** Searching for local proof support is not unique to Litex:
> [Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/),
> [Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html),
> and [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) provide local automation through explicit tactics or
> proof methods; [Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf)
> has empty justification;
> [ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM) can attempt to prove a theorem event without hints; and
> [Naproche](https://naproche.github.io/) uses automated theorem provers
> to check proof steps written in controlled natural language. Litex tests a more specific hypothesis: can bounded,
> fact-triggered local justification become the default semantics of ordinary mathematical statements, with a verified fact
> written back into the context and its verification source displayed after success?

<a id="goal-3"></a>
<a id="bottom-up"></a>
<a id="two-directions"></a>

## 3. Building Proof Flow Bottom-Up

Fact-oriented answers the question “what is one line of Litex source?” It is a mathematical fact waiting for the kernel to verify. Bottom-up answers “how do those facts compose into a proof?” Every verified fact extends the context, allowing later facts to grow from earlier results.

Litex proofs proceed bottom-up. The default unit of reasoning is the next mathematical fact in the current context, not an active Goal that every line must immediately advance. As long as a statement is in the current scope, is well-defined, and has sufficient support in the existing context, the kernel can accept it, store it, apply currently relevant inference rules, and pass the enriched context to later statements. Several mathematical branches can grow separately before later statements bring them together.

Lean's usual interactive theorem proving is goal-directed, with a typical direction that is backward and top-down. The final theorem first fixes the final Goal. Local terms and tactic commands are elaborated under that expectation, progressively decomposing the Goal or reducing it backward to simpler subgoals until Lean can assemble a complete proof term.

The default questions can be summarized as follows: Lean asks, “How can I simplify the current Goal until it reduces to known conditions?” Litex asks, “Given the known conditions, what fact can I derive next?”

> Think of writing a proof as building with LEGO bricks. At the start, we have a collection of available pieces and know what the final model should be. A typical Lean tactic workflow is like beginning with the finished model and disassembling it backward until the requirements can be met by the pieces at hand. A typical Litex workflow starts from the available pieces and builds forward, allowing one verified local result after another to converge on the final model. This analogy describes only the default direction of development. It does not imply that Litex has a weaker verification standard, nor that either system can work in only one direction.

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

#### Example 2: Set Inclusion

The preceding example used algebraic rewriting. To show that the difference in interaction direction does not depend on computation, consider a second example that transports membership along set inclusions. Lean begins from the target `x ∈ c` and progressively states, with `apply`, how it should be proved:

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

Litex instead states the intermediate result and final result that should be established, and the kernel searches for their support in the current context:

```litex
forall A, B, c set, x A:
    A $subset B
    B $subset c
    =>:
        x $in B
        x $in c
```

Lean has a powerful Infoview that lets the user see the Goals remaining after each tactic:

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

Litex's runner trace instead shows why each conclusion holds:

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

Beyond the difference between bottom-up and top-down workflows, the output reveals the interface distinction again: Litex source states *what to verify*, and its kernel searches for *how to verify it*. Lean tactic source states *how to transform the current proof state*, while the resulting Goals show *what remains to be verified*.

<details>
<summary><strong>Further reading: how bottom-up proof flow helps AI write formal code</strong></summary>

An unfinished formal proof need not be worthless. In a common Goal-directed Lean workflow, an incomplete attempt appears primarily as a Goal that remains unsolved. Lean's Infoview and error messages can expose the current proof state, and users can deliberately preserve intermediate results as lemmas, but the exploration does not by default become a durable mathematical record of which facts were established, where support first ran out, and how far the argument had progressed. This is a distinction between default workflows and artifacts, not a claim that Lean cannot express forward proofs or save intermediate results.

In Litex's bottom-up workflow, every accepted statement extends the current context as a verified fact. If the next statement is `unknown`, the verified prefix remains available and the boundary of the failure is attached to that specific mathematical statement. A partial proof can therefore remain as **a sequence of verified facts plus an explicit `unknown` boundary**, rather than collapsing into an undifferentiated failed script. The correct part of an unfinished attempt can be retained, inspected, reused, and continued later.

This changes the interaction loop for AI. A model can propose the next mathematical fact, receive local verification feedback, keep a successful step, and revise at the first `unknown`. It does not need to generate an entire proof correctly in one pass. The accumulated facts, their verification sources, and the explicit stopping point provide structured experience for the next attempt, whether it is made by the same model, another model, or a human.

Bottom-up organization alone does not solve proof search, and the usefulness of a failure report still depends on the quality of the kernel's diagnostics. Its intended value is more specific: **even when a formalization is unfinished, its verified progress and precise point of uncertainty can remain first-class, reusable results.**

</details>

> **Put sharply: a common Lean tactic workflow can feel like being required to read a mathematics book from its final page or write a paper from its final page—fix the ultimate Goal first, then work backward to infer what must precede it.**

> **Equally sharply, from first principles Litex's largest current problem is that its trusted kernel is too large. Litex places hundreds of common proof patterns into builtin and infer rules, moving work from user proof scripts into the trusted computing base. The proof work has not disappeared; the system has absorbed it. For a smaller and relatively independent trusted boundary—the Lean kernel—to recheck Litex's results, Litex must compile its recorded verification paths into Lean proof terms. Extending that compilation coverage is feasible, but it will take time and careful engineering.**

> **Position in the design space.** Mizar and Isar already support forward, declarative proof text; ACL2 accumulates
> a reusable theorem database; and Naproche checks mathematical statements incrementally. “Growing bottom-up” is therefore
> not by itself Litex's differentiating claim. Litex tests a particular combination: an ordinary fact is an executable unit
> that extends the context; local justification starts without a separate proof-method invocation; and explicit proof
> structure appears only when ordinary reconstruction reaches its boundary.

<a id="compatibility"></a>

## 4. Lean-Compatible: A Concise Mathematical Front-End Language for Lean's Trusted Ecosystem

Litex is first an independently usable formal language. It has its own syntax, runtime, and kernel. Even when a Litex mathematical document is not compiled to Lean, Litex can directly check its well-definedness and facts and provide local proof feedback. “A mathematical front-end language for Lean” therefore means that the Litex-to-Lean compiler translates the verification paths it currently supports into Lean proof terms, expanding its coverage incrementally to connect with the Lean ecosystem. *I hope Litex's development can provide the Lean community with new formal mathematical content and interface experience, while Lean's kernel and Mathlib ecosystem can in turn strengthen Litex. The relationship is complementary, not competitive.*

This complementary relationship begins at the authoring interface. Litex was designed from the outset as a language specialized for mathematics; its syntax and interaction contract are closer to mathematics itself than to the abstractions of a general-purpose programming language. Users can focus on mathematical objects, conditions, intermediate facts, and conclusions while receiving fast, local, and traceable verification feedback from the kernel. This matters for AI as well: a generative system can make small-step suggestions around “the next mathematical fact that should hold,” then revise them using the kernel's concrete justification or failure boundary, instead of immediately lowering the entire mathematical intent into the details of elaboration, type classes, namespaces, and tactic calls. Those mechanisms are, of course, important sources of Lean's expressiveness and compositionality and are necessary for Lean as a general-purpose programming language.

*The compiler gives this relationship a second role: an important independent safeguard for Litex's rigor.* The Rust source under Litex's `src/` directory alone currently contains roughly 210,000 lines, and that surface continues to grow with hundreds of builtin and infer rules and new capabilities. Auditing such a large trusted implementation is naturally harder than auditing Lean's much smaller kernel. When a Litex verification path can be compiled in full into a Lean proof and accepted by the Lean kernel, it supplies strong, independent correctness evidence for that covered path and substantially reduces reliance on Litex's own large implementation as the sole basis of trust.

_This remains a goal that Litex is implementing and testing, not a capability already achieved comprehensively by the current beta. The Litex-to-Lean compiler currently covers only some verification paths. Its first-principles design and framework are in place, but many details still need work. Community feedback and contributions are welcome._

<details>
<summary><strong>Further reading: how the Litex-to-Lean compiler works</strong></summary>

*This subsection explains the implementation mechanism and current correctness boundary in more detail. Skipping it will not affect the rest of the blueprint.*

The architectural route follows from these complementary roles. Litex is based on set theory, and Lean's Mathlib includes substantial support for set-theoretic mathematics. Litex's verification system saves users from writing many proof-construction steps themselves, but the verifier records the route it used. In principle, each supported recorded step can be represented by an appropriate Lean theorem or proof construction and assembled into a proof term. That is why a Litex-to-Lean compiler is a natural architectural goal.

Making that route concrete requires a mapping to Lean and Mathlib. For verification, the compiler maps each supported Litex verification path to the corresponding Lean proof construction. For mathematical objects, it maps each Litex object to a Lean representation—not by translating it directly, but by using designed wrappers as an intermediary. This mapping is feasible, but it takes time to develop and verify. The intermediary code lives at https://github.com/litexlang/golitex/blob/main/lean/Litex/Core.lean and remains under active development.

A small numerical theorem illustrates both the evidence-preserving mapping and
the desired ecosystem interface. Consider this checked Litex theorem:

```litex
thm litex_real_add_comm:
    ? forall a, b R:
        a + b = b + a
```

This gives the theorem two target views. The canonical compiler theorem keeps the Litex
classification and verification evidence:

```text
∀ {α β : Type} (a : α) (ha : Litex.In a Litex.R)
  (b : β) (hb : Litex.In b Litex.R),
  Litex.Same
    ((Litex.In.rep a ha : ℝ) + (Litex.In.rep b hb : ℝ))
    ((Litex.In.rep b hb : ℝ) + (Litex.In.rep a ha : ℝ))
```

When those wrappers have a reviewed, lossless elimination route, the compiler
should additionally expose the ordinary Lean corollary:

```text
theorem litex_real_add_comm (a b : ℝ) : a + b = b + a
```

The canonical theorem preserves Litex proof provenance; the native corollary
is what a Lean user can apply, rewrite with, and combine with Mathlib. The
corollary must be derived through proved wrapper bridges, not fresh Lean proof
search, and is omitted when no lossless route exists. This two-layer public
interface is a confirmed compiler direction, not yet a fully implemented
capability.

**The practical payoff of that second view is interoperability: once a Litex definition
or theorem is within the compiler's supported, losslessly unwrappable surface,
it can enter the Lean ecosystem with little friction. Lean users can import
and reuse its native interface without leaving their familiar Lean/Mathlib
workflow or first learning Litex from the ground up.**

This example also exposes the compiler's two underlying design problems. The first is theoretical: how to represent Litex mathematics in Lean and Mathlib. The same mathematical object or statement can often be expressed by several Lean formulations with the same mathematical meaning, but the choice has long-term consequences for whether generated code can reuse Mathlib naturally, how later Litex features can be extended, and how well the Litex and Lean ecosystems can work together. Foundational concepts such as functions, sets, membership, and well-definedness therefore need a consistent and sustainable representation—not merely one that makes today's examples pass.

The second problem is practical: how to turn the information produced by successful Litex kernel execution into Lean proofs. Litex verification decomposes a goal into smaller subgoals along a search tree; a successful branch must return structured information from the leaves to the root, recording the rules, facts, mathematical objects, subproofs, and well-definedness results involved. Declarations, objects, facts, and scope changes produced during statement execution must be preserved as well, allowing the compiler to replay the verification route Litex already found deterministically instead of reconstructing a proof from display text or asking Lean to search for another one.

</details>

<a id="conclusions"></a>

## Conclusion

Litex aims to make writing and verifying formal mathematics closer to everyday mathematical thought. By offering syntax and an interaction contract closer to ordinary mathematical writing, Litex seeks to lower the barrier to formal authorship and review, make mathematical text executable, and support deeper mathematical understanding and discovery.

Programming languages repeatedly create new layers of abstraction. C usually lets programmers avoid arranging assembly instructions one by one. Higher-level languages such as Python absorb still more routine work, including much manual memory management and the requirement to declare types for most variables in advance.

In this sense, Litex attempts to provide an abstraction layer for routine proof connections through hundreds of common builtin rules together with matching and substitution by fact shape. Litex's rich verification mechanisms, the mathematical objects and statements it exposes to users, and those it deliberately does not expose can all be understood as attempts to keep user source at the level where mathematical thought actually occurs. Lean is based on abstract type theory and is powerful, but it exposes many details. Litex is based on a more familiar mathematical axiomatic foundation and a more familiar direction of verification, sparing users many details that are unnecessary for its chosen task. Lean has corresponding strengths: a small kernel, strong compositionality, and a rich ecosystem. Litex is still developing, and its own source-level rigor can be strengthened by compilation to Lean.

> **A personal analogy.** When we inspect machine code generated from C, a surprisingly large part of the listing can consist of address information—sometimes seemingly close to half. Lean source likewise often records theorem names or identifiers so that the system knows which result to invoke. Litex tries to keep the mathematical facts themselves at the center of the source and reduce this kind of bookkeeping noise.

As humans and AI collaborate to create and accumulate more mathematical knowledge, formal systems should explore more than one way to write and verify that knowledge. Considering only the default direction of interaction, Litex can in a limited sense be viewed as “Lean in reverse.” This design path is not intended to replace Lean. It offers another idea worth practicing and testing for how humans and AI might write formal mathematical code.

Along this path, Litex's potential value can be understood at three connected levels:

1. **First, lower the barrier to writing and reviewing formal mathematics.** Litex tries to keep formal source close to mathematics that people can understand directly, so authors and reviewers can inspect its objects, premises, reasoning spine, and conclusions. This is especially important for AI-generated source: a verifier can check only the proposition that was actually written, while readable semantics let humans judge whether that proposition faithfully expresses the original mathematical intent.
2. **Then make mathematical text executable.** When definitions, lemmas, and proofs remain readable and reviewable as mathematical exposition, they can also be checked by machines and reused across files and chapters. Only then can formal verification gradually move toward textbooks, teaching, and scientific writing instead of remaining only within proof-assistant engineering for experts.
3. **Promote deeper mathematical understanding and discovery.** If formal languages make mathematics genuinely engineerable, and if more people gain access to them, I believe mathematicians, students, and AI will understand the relationships among mathematical objects, definitions, theorems, and proofs at a deeper level. That understanding may accelerate mathematical discovery and even support new mathematical paradigms.

Related links:

1. To try examples directly and inspect Litex's output and knowledge graphs, visit [litexlang.com](https://litexlang.com).

2. For the kernel implementation, see the [golitex repository](https://github.com/litexlang/golitex).

Note: At the current research stage, Litex develops its research program and explains its goals in public. The repository therefore contains checked results, experiments, and unfinished work side by side. *Publicly visible does not mean claimed complete.* Each capability should be judged by its current tests, dated status notes, trusted boundary, and known limitations.
