# Litex: A Formal Language Where Mathematics Verifies Itself

Created and maintained by Jiachen Shen.

Last updated: September 2, 2026.

Website: https://litexlang.com/doc/Litex_Blueprint

Chinese version: https://litexlang.com/doc/Litex中文蓝图

Litex is a set-theoretic, fact-oriented formal language that builds proof flows
from the bottom up. It puts humans, AI, and the verifier in the same loop:
humans provide mathematical intent, AI proposes or repairs the next fact, and
Litex checks it and returns either its supporting evidence or the point where
verification stops. Through this cycle, checkable mathematical knowledge
accumulates. In principle, any Litex code can be compiled to Lean and connected
to the Lean/Mathlib ecosystem.

> **Litex is an experimental hobby project in beta; expect rough edges.**

<!-- Blueprint spine: reasoning abundance → scientific object → design hypothesis → measurable costs → potential capacity impact → verification and understanding bottlenecks → two participation barriers → four language choices → definition and verification → ToLean/adapter handoff → the end-to-end human–AI–Litex verification loop → ecosystem role → success criterion -->

<!--
Litex 定位四层检查（写作时逐层核对；面向不同受众可以调整强调重点，但不能混淆层级）：
- 科学对象：可检查知识如何被表示和逐步构造。
- 科学假设：事实导向表示与事务式交互是否构成新的形式语言范式。
- 科学结果变量：这种范式怎样影响构造、理解、审核、修复和复用知识的成本。
- 社会影响：降低门槛，使验证能力跟上 AI 产生候选推理的速度。
写作边界：前三层是 Litex 的科学内核；第四层是潜在影响。不得用“从而”把未验证的科学结果写成已经实现的工具效果。
-->

## Table of Contents

- [Litex: A Formal Language Where Mathematics Verifies Itself](#litex-a-formal-language-where-mathematics-verifies-itself)
  - [Table of Contents](#table-of-contents)
  - [Litex Blueprint Overview](#litex-blueprint-overview)
    - [Two Barriers: From Understanding Mathematics to Being Able to Formalize It](#two-barriers-from-understanding-mathematics-to-being-able-to-formalize-it)
  - [1. Based on Set Theory: Keep Mathematical Objects Readable](#1-based-on-set-theory-keep-mathematical-objects-readable)
      - [Lean: A Record over `Type` and Curried Functions](#lean-a-record-over-type-and-curried-functions)
      - [Litex: Operations on a Set and Structural Facts Written Directly](#litex-operations-on-a-set-and-structural-facts-written-directly)
  - [2. Fact-Oriented: Source Preserves *What Holds*](#2-fact-oriented-source-preserves-what-holds)
    - [Why Do Ordinary Facts Need Neither Names nor Tactics?](#why-do-ordinary-facts-need-neither-names-nor-tactics)
      - [1. Match Fact Shapes with Builtin Rules](#1-match-fact-shapes-with-builtin-rules)
      - [2. Match with User-Provided Universal Facts](#2-match-with-user-provided-universal-facts)
      - [3. Match with Concrete Facts and Known Equalities](#3-match-with-concrete-facts-and-known-equalities)
    - [Summary: Put *What to Prove* in the Source and Leave the Search for *How* to the Kernel](#summary-put-what-to-prove-in-the-source-and-leave-the-search-for-how-to-the-kernel)
  - [3. Bottom-Up: Let Verified Facts Continue to Grow](#3-bottom-up-let-verified-facts-continue-to-grow)
  - [4. Lean-Compatible: Independent Rechecking for Covered Paths](#4-lean-compatible-independent-rechecking-for-covered-paths)
    - [One Complete Theorem Now Reaches Lean](#one-complete-theorem-now-reaches-lean)
  - [From Four Design Principles to Mathematical Practice: Definition and Verification](#from-four-design-principles-to-mathematical-practice-definition-and-verification)
  - [The End-to-End Human–AI–Litex Verification Loop](#the-end-to-end-humanailitex-verification-loop)
  - [From Language to Ecosystem: The Role Litex Aims to Play](#from-language-to-ecosystem-the-role-litex-aims-to-play)
  - [Conclusion](#conclusion)
    - [Related Links](#related-links)

<a id="overview"></a>

## Litex Blueprint Overview

AI is rapidly lowering the cost of reasoning, proof, and scientific exploration. Humans and AI can now propose many arguments and conjectures quickly. But answers that *look right* are not reliable knowledge. Candidate conclusions are growing faster than we can check them. This is **reasoning overflow and validation crisis**.

Litex studies how checkable knowledge should be represented and constructed step by step. It tests whether facts as the basic unit, with immediate checking and local rollback as the interaction mechanism, can form a new design paradigm for formal languages; it further measures how this paradigm affects the cost for humans and AI to construct, understand, audit, repair, and reuse checkable knowledge. If supported, the hypothesis could lower the barrier to using formal languages and help rigorous verification capacity keep pace with the growth of candidate reasoning in the AI era.

Correctness is only half of the crisis. A proof can be correct but hard to read, explain, connect, or reuse. Mathematicians and formal-language communities talk about complexity every day: long proofs, distant representations, steep tools, and hard-to-digest results. Yet they rarely ask why understanding bears this cost—or how to reduce it. This is the **complexity tax on understanding**.

Not all complexity can disappear. Some belongs to the mathematics. Some is added by representations, evidence plumbing, and interaction. With abundant AI-generated reasoning, the distinction matters twice: can the result be verified, and can humans understand, digest, and reuse it?

Terence Tao's [2026 ICM public lecture](https://teorth.github.io/tao-web/slides/age-of-ai-icm-2026.pdf) and [companion essay](https://arxiv.org/abs/2608.16753) show the same bottleneck. Generation and verification can outpace exposition, digestion, community acceptance, and canonicalization. This context motivates Litex's question but does not answer it; the representation-and-interaction hypothesis above is Litex's own.

Education, science, engineering, and AI review all need formalization. Turning AI's creativity into trustworthy knowledge requires wider participation.

> **The next step for formal languages is not only to give existing experts stronger tools. It is also to help more people become experts.**

People who understand a domain should be able to express, check, and repair its formal reasoning—and review AI-generated work directly.

**Litex tests that path. It is a set-theoretic, fact-oriented, bottom-up formal language compatible with Lean.** Humans and AI write facts directly and see their verification grounds or stopping point. Litex lowers not rigor, but the barrier to reaching it.

### Two Barriers: From Understanding Mathematics to Being Able to Formalize It

The next two examples show two sources of the complexity tax. Both are trivial for Lean. They separate two interface barriers; they do not compare mathematical power.

1. **Entry knowledge:** users may know a fact but still need imports, proposition syntax, type annotations, and tactics.
2. **Representation distance:** even after learning the tool, users may manipulate subtypes and proof arguments instead of writing as they ordinarily reason.

These mechanisms support Lean's generality, compositionality, and ecosystem. Litex explores a different front-end contract: conditions remain explicit and strict, while the system manages more evidence and representation detail.

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

The difficulty is not `1 + 1 = 2`. It is knowing `Mathlib`, `example`, the type annotation, and `norm_num`. These matter in complex proofs but are not part of this fact's mathematics. Must they be prerequisites when the user already understands the claim?

The second example shows representation distance. For a function on the positive reals, one common Lean encoding is:

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

**This only says that a function value equals itself.**

In the Lean subtype encoding, applying `f` packages `hx : x > 0` with `x` as `⟨x, hx⟩`. Litex still checks `x > 0`, but its source retains the ordinary `f(x)`.

> **Users write mathematics; the system manages verification evidence. Conditions cannot be omitted, but certificates need not be threaded by hand.**

This does not lower verification standards. It lets an abstraction layer absorb mechanical detail and lower the tool barrier.

AI also creates a subtler failure: generated Lean code passes the kernel, but its proposition may omit a condition, change a quantifier, or weaken the conclusion. The Lean kernel is not at fault; it checked the encoded proposition correctly. The mismatch is between formal specification and mathematical intent.

If a formal statement has a high reading barrier, the relevant domain expert may miss that *the proof is correct but the problem was encoded incorrectly*. Lowering that barrier therefore expands AI review capacity, not just convenience.

Litex asks whether students, domain experts, and AI can produce checked mathematics more easily without lowering verification standards.

The path for this experiment is:

1. **Set theory:** objects are organized through sets and membership, separately from facts about them. Lean's `Set α` first depends on `α : Type*`; Litex chooses a more direct set-theoretic surface.
2. **Fact-oriented:** source states *what holds*; the kernel searches rules, known facts, and equalities while checking well-definedness. Typical Lean tactics describe how to handle the current Goal.
3. **Bottom-up:** Litex lets verified facts extend the context; common Lean tactic interaction reduces the final Goal backward. Both can express the other direction.
4. **Lean-compatible:** the compiler translates covered Litex verification routes into Lean proof terms. Coverage remains partial; not every Litex source compiles today.

The two workflows can be simplified as follows:

```text
Lean: proposition → Goal → tactics and elaboration → proof term → kernel check
Litex: objects and facts → kernel checks and searches for justification → verified facts extend the context
```

Ideally, users focus on objects, conditions, facts, and conclusions while Litex acts as a copilot with fast, local, traceable feedback. *People who understand a domain but are not proof-assistant specialists can still enter formal reasoning.*

> **Lean supports other encodings and forms of automation as well. The comparison here concerns source interfaces, not whether the two languages can express the same proposition.**

> **This is a design direction, not a claim that the current language, standard library, or compiler is complete.**

<a id="set-theory"></a>

## 1. Based on Set Theory: Keep Mathematical Objects Readable

For formal semantics to be precise yet directly reviewable, the first question is which objects source presents first. Litex chooses sets, membership, and relations between sets. A set-theoretic problem can therefore state sets, subsets, and intersections without first introducing a carrier type.

The following Litex code states that intersection is monotone with respect to inclusion:

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

This is a complete fact submitted to the kernel, not a proof hole. Its ordinary reading is: a member `x` of `intersect(s, u)` belongs to `s` and `u`; since `s $subset t`, it belongs to `t` and thus to `intersect(t, u)`. The user states the result, while the kernel searches through unfolding, membership transport, and reassembly.

<details>
<summary><strong>Full comparison: how Lean develops the same set-theoretic proposition</strong></summary>

Here is the version from the set-theory chapter of *Mathematics in Lean*:

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

Lean first declares `α : Type*`, then `s`, `t`, and `u` as values of `Set α`. Here `Set α` is a predicate over `α`; `Type*` and its universes provide a more general type-theoretic organization that supports reuse over arbitrary carriers.

Litex chooses a different boundary: sets and membership form its surface, with specialized syntax and verification paths for membership, subsets, intersections, and unions. Here the user only declares three sets with `set` and writes the expected inclusion.

This is not a claim that shorter code is stronger: Lean can use a shorter proof or automation, while the example preserves the textbook's unfolded route. The comparison is between default interfaces. Lean gives sets a type-theoretic carrier before constructing a proof; Litex directly recognizes and checks common set-theoretic facts.

</details>

<details>
<summary><strong>Technical summary: typing judgments and membership facts</strong></summary>

Lean organizes mathematics around typed terms: after elaboration, a core expression is checked through a judgment of the form `Γ ⊢ e : T`. The colon belongs to this metalevel typing judgment; it is not an ordinary proposition inside Lean that accumulates alongside equality, order, or theorem facts. Surface overloading and coercions may elaborate similar notation into different core terms, but each resulting term is checked at a definite type.

Litex instead organizes mathematics around objects and a growing context of facts. `e $in S` is an object-language membership fact, on the same logical side of the boundary as equality, order, and other predicates. The same object may therefore be proved to belong to many unrelated or overlapping sets: membership is a relation between objects, not a unique intrinsic assignment `typeOf(e) = S`.

This does not remove static discipline or inference. Litex checks domains, return sets, structure fields, and other well-definedness obligations before accepting an expression, and dedicated rules infer membership and carrier facts throughout a proof. The distinction is that this inference extends the context with facts such as `e $in S`; it does not infer one privileged type `e : T` that determines the object's identity.

</details>

The set-theoretic surface does not remove constraints. Function domains and codomains, structure fields, and membership still undergo well-definedness checks, placed where mathematicians would naturally write them. `template` supports families indexed by carriers, parameters, or hypotheses; Litex does not claim to be a complete dependent type theory.

Nor must authors repeat well-definedness transport at every call. A checked function contract—parameter domains, return set, and call conditions—becomes reusable. The verifier checks arguments, derives return membership, and carries it through nested calls.

The obligation remains; only repeated transcription disappears. Given `f : A → B`, `g : B → C`, and `a ∈ A`, one simply writes `g(f(a))`.

<a id="group-comparison"></a>

<details>
<summary><strong>Small example: build a group and its mathematical interface from common foundations</strong></summary>

When a standard library does not yet cover a domain, can users build its theory from a small set of common concepts? Sets, functions, relations, and operations form a cross-domain language in which definitions and theorems can grow along their mathematical dependencies instead of first conforming to an external encoding. This is **bootstrapping a mathematical theory**.

Mature libraries can accelerate construction, but they should not determine the boundary of expression. The two fragments below describe the same group and identity-uniqueness result through different interfaces to carriers, operations, and laws.

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

This Lean record begins with `Carrier : Type`; its elements, operations, and laws depend on that carrier. `Carrier → Carrier → Carrier` is a curried binary operation, while laws become named fields such as `mul_assoc` and `one_mul`. This supports abstraction and precise library reuse, while requiring authors to select theorem names, variants, and equality directions. The example explicitly invokes `G.one_mul`.

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

Litex binds a nonempty set `s` and models a group on it. `mul fn(x, y s) s` is a closed binary operation; laws appear as ordinary facts inside `<=>:`. Identity uniqueness is then a direct equality chain, with the kernel finding the needed laws and directions. Long-lived results may still be named `thm`; ordinary laws and local facts need not first enter a naming interface.

Structural laws are not released without bounds; Litex first checks structure membership and scope.

<details>
<summary><strong>Implementation note: the release boundary for struct facts</strong></summary>

A field path such as `G.mul` is checked against the declared struct carrier; this alone does not add group laws to context. The binder `G &Group<s>` opens exactly one layer. Function results or nested struct fields require `by struct def expression`, which verifies membership before releasing that layer. A later standalone `expression $in &Group<s>` remains opaque.

</details>

Lean can of course define a group without Mathlib's existing interface; the comparison concerns the default experience, not expressive limits. “Building from the ground up” is not dependency-free: Litex still relies on its kernel, rules, and standard library. External libraries remain important accelerators without becoming expressive boundaries.

The group is only a small demonstration. A stronger test is whether a small team can build a readable, extensible interface with explicit boundaries for an under-covered domain. Future geometry and other libraries should report dated source, verifier results, `trust` boundaries, and real reuse rather than treating that outcome as established in advance.

</details>

> **Position in the design space.** Set-theoretic presentation is not unique to Litex:
> [the Mizar Mathematical Library](https://wiki.mizar.org/library/) is based on Tarski–Grothendieck set theory;
> [Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) and
> [Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) expose dependent type-theoretic kernels to users; and
> [Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
> uses polymorphic higher-order logic.
>
> Litex's proposition language is broadly first-order in flavor: atomic relations and named predicates are organized by restricted classical forms and quantifiers. It favors canonical fact shapes, and propositions and proofs are not arbitrary first-class values.
>
> This describes only the proposition interface; the verifier also checks well-definedness and searches definitions, context, and supported rules for grounds.
>
> Against that background, Litex asks a more specific question about the user-facing object interface:
> can a small, membership-centered, set-theoretic surface cover substantive mathematics without first requiring users to manage type universes?

<a id="fact-oriented"></a>

## 2. Fact-Oriented: Source Preserves *What Holds*

Fact orientation reallocates work: source preserves the objects and facts that should hold, while the kernel finds, checks, and explains local justification.

The earlier set-inclusion and group examples gave two small versions of this division: the user states the desired relation or structural fact, and the kernel searches for local support. This section first isolates that interface. A full convergence example after the four principles will combine definitions, quantifiers, witnesses, and a continuous estimate.

### Why Do Ordinary Facts Need Neither Names nor Tactics?

An ordinary fact such as `a + b >= 0` needs no dedicated name. The user does not specify a tactic, library theorem, or rewrite direction line by line; they state the desired fact, and the kernel searches rules and context for support.

> **The core human–machine division of labor in a fact-oriented system is: the user writes “what I want to prove”; Litex searches for “how this fact can be verified.”**

Litex matches proof support and explains the path. Lean follows tactics to elaborate a proof term, shows remaining Goals in the Infoview, and checks the term in the kernel.

Litex does not forbid names. Classic theorems, library interfaces, and explicit dependencies may be `thm` definitions, invoked with `release thm` or selected with `by thm ... => fact`.

Ordinary facts need neither names nor tactics because the kernel searches by predicate, argument shape, and context. Sources include builtin or user-provided universal facts, concrete facts, and equality information; other optimizations do not change this division.

<details>
<summary><strong>Expanded: how the kernel searches for a verification path by fact shape</strong></summary>

#### 1. Match Fact Shapes with Builtin Rules

An atomic fact is a predicate plus arguments—the predicate like a verb, its arguments like the nouns involved. For example:

```text
a + b >= 0
```

Its predicate is `>=`; its arguments are `a + b` and `0`, with addition on the left and zero on the right. The kernel narrows candidates from this shape without first knowing a fact name.

For example:

```litex
have a R = 1
have b R = 2

a + b >= 0
```

Seeing `>=`, left-side addition, and right-side zero, the kernel tries this builtin nonnegativity rule:

```text
forall x, y R:
    x >= 0
    y >= 0
    =>:
        x + y >= 0
```

Matching yields `x := a` and `y := b`. The kernel checks `a $in R`, `a >= 0`, `b $in R`, and `b >= 0`, then accepts the target.

#### 2. Match with User-Provided Universal Facts

Candidates can also be ordinary `forall` facts the user proved or assumed:

```litex
abstract_prop p(x)

trust forall a R:
    $p(a)

$p(1)
```

For `$p(1)`, the kernel finds `$p(a)`, matches `a` to `1`, and checks the instantiated requirement `1 $in R` before accepting the target.

`abstract_prop` declares a predicate without a definition. `trust` warns that a fact was accepted without verification; an artifact containing it is not fully checkable. It can mark external assumptions or proof debt.

#### 3. Match with Concrete Facts and Known Equalities

A third source is an already known concrete fact:

```litex
abstract_prop q(x)

forall a R:
    $q(a)
    a = 1
    =>:
        $q(1)
```

To verify `$q(1)`, the kernel finds `$q(a)`. The contextual equality `a = 1` makes the arguments match, allowing transport to `$q(1)`.

</details>

### Summary: Put *What to Prove* in the Source and Leave the Search for *How* to the Kernel

This resembles everyday mathematics: authors write the desired conclusion, and readers infer its support from context and known facts instead of seeing every theorem, equality, or definition named.

<details>
<summary><strong>A personal analogy: imperative and declarative styles</strong></summary>

As a rough distinction, programming languages have imperative and declarative styles. Imperative code, common in C and Rust, emphasizes *how*. Functional languages such as Haskell emphasize *what*.

Here is the interesting tension: Lean itself is functional and declarative, yet tactic proofs often read imperatively. Each command changes the current Goal. Litex shifts the default proof interface back toward *what*: the author states the next fact, and the verifier searches for *how* to justify it.

</details>

> **Position in the design space.** Searching for local proof support is not unique to Litex:
> [Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/),
> [Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html),
> and [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) provide local automation through explicit tactics or
> proof methods; [Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf)
> has empty justification;
> [ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM) can attempt to prove a theorem event without hints; and
> [Naproche](https://naproche.github.io/) uses automated theorem provers
> to check controlled-natural-language steps. Litex asks more specifically whether ordinary mathematical statements can trigger local justification bounded by context and supported rules, then enter the context with their verification source displayed.

<a id="bottom-up"></a>

## 3. Bottom-Up: Let Verified Facts Continue to Grow

Mathematical facts are the basic units of Litex source. Each verified fact extends context for later statements, so proof flows from known conditions toward the conclusion. This is “bottom-up.”

Litex supports **declarative proof writing whose default flow is mostly forward reasoning**. Its unit is the next fact in context, not an active Goal every line must advance. A scoped, well-defined, supported statement can be accepted, stored, and used by applicable rules; branches may grow separately before converging.

Lean's typical interaction is goal-directed, backward, and top-down: the theorem fixes the Goal, then terms and tactics reduce it to simpler subgoals until Lean assembles a proof term.

Lean asks, “How can I reduce this Goal to known conditions?” Litex asks, “Given known conditions, what fact follows next?”

> Think of proof as LEGO. Lean tactics typically disassemble the desired model until its requirements match available pieces; Litex typically builds forward from those pieces until verified results converge on the model. This describes default direction only: Litex's standard is not weaker, and neither system is limited to one direction.

<a id="two-directions"></a>

<details>
<summary><strong>Small example: top-down and bottom-up forms of the same algebraic equality</strong></summary>

This example develops one equality in two directions. Lean begins from the Goal; each `rw` specifies a fact, matching direction, and replacement:

```lean
-- Using facts from the local context.
example (a b c d g f : ℝ) (h : a * b = c * d) (h' : g = f) :
    a * (b * g) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

Litex reverses the four rewrites into one chain, from `c * (d * f)` through intermediate results to `a * (b * g)`:

```litex
claim:
    ?forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    c * (d * f) = (c * d) * f = (a * b) * f = a * (b * f) = a * (b * g)
```

The four equalities correspond to `rw [mul_assoc]`, `rw [h]`, `rw [← mul_assoc]`, and `rw [h']`, in reverse order from the Lean script. Lean specifies how to rewrite the Goal; Litex states the facts that should hold along the route, and the kernel searches for support for each adjacent equality.

</details>

Bottom-up progress can accumulate: separately accepted statements remain a verified prefix, while the next `unknown` marks the repair point. Accepted parts can be reused, but a composite statement with a failed internal conclusion is not partially committed.

This convenience has a trust cost. Hundreds of builtin and infer rules move work from user scripts into a larger trusted computing base. The obligation has moved, not vanished; recorded routes must therefore be handed to Lean's smaller kernel for covered-path rechecking.

<details>
<summary><strong>Position in the design space: forward proof is not unique to Litex</strong></summary>

Mizar, Isar, ACL2, and Naproche already support forward text, theorem accumulation, or incremental checking. Litex instead tests their combination: an ordinary fact triggers local verification and extends context on success, while explicit proof structure appears only when ordinary automation is insufficient.

</details>

<a id="compatibility"></a>

## 4. Lean-Compatible: Independent Rechecking for Covered Paths

Litex is first an independently usable language with its own syntax, runtime, and kernel; without Lean it still checks well-definedness and facts and provides feedback.

“A mathematical front end for Lean” means translating supported verification paths into Lean proof terms while coverage expands. *Litex can offer content and interface experience; Lean's kernel and Mathlib can strengthen Litex. The relationship is complementary, not competitive.*

Fact-first verification lets humans and AI focus on objects, conditions, facts, and conclusions with local traceable feedback. Elaboration, type classes, namespaces, and tactics are instead important sources of Lean's expressiveness and compositionality.

*The compiler also provides an independent safeguard for Litex's rigor.* Rust under `src/` alone approaches 200,000 lines and contains hundreds of growing rules, making its trusted surface harder to audit than Lean's smaller kernel. A Litex route fully compiled and accepted by Lean gains strong independent evidence and reduces sole reliance on Litex's implementation.

_Coverage remains partial. Only source routes that fully compile and pass Lean receive this safeguard._

### One Complete Theorem Now Reaches Lean

The convergence theorem below is no longer only a Litex example. ToLean compiles the recorded evidence for `converges_to_mul_const` into Lean. The Lean kernel accepts it, and a handwritten adapter exports a native Mathlib `Filter.Tendsto` theorem.

The decisive Lean call is short:

```lean
import LitexGenerate

have generated :=
  __Compiler_main.converges_to_mul_const s sIn a aIn c cIn h
```

**Litex source ✓ → generated Lean ✓ → Lean kernel ✓ → Mathlib adapter ✓**

[See the complete showcase in the repository](https://github.com/litexlang/golitex/tree/main/showcases/litex_to_lean_mathlib_pipeline/showcase2).

This establishes one fully covered route, not universal compiler coverage.

<details>
<summary><strong>How the Litex-to-Lean Compiler Works</strong></summary>

Ecosystem reuse and independent rechecking share one route: Litex records verification paths, maps each supported step to a Lean theorem or proof construction, and assembles a proof term. Mathlib's set-theoretic support makes this a natural architecture.

Implementation requires two mappings: supported paths to Lean proof constructions, and Litex objects through designed wrappers to Lean representations rather than mechanical translation. This takes continued development and verification; intermediary code lives at https://github.com/litexlang/golitex/blob/main/lean/Litex/Core.lean.

The compiler has two underlying problems. First, how should Lean/Mathlib represent Litex mathematics? Equivalent formulations have long-term consequences for Mathlib reuse, Litex extension, and ecosystem cooperation. Functions, sets, membership, and well-definedness need a consistent, sustainable representation.

Second, how should successful execution become a Lean proof? A search branch must return structured rules, facts, objects, subproofs, and well-definedness results, while preserving declarations and scope changes. The compiler can then replay Litex's route deterministically instead of rebuilding from display text or asking Lean to search again.

</details>

Litex therefore supplies a mathematics-facing interface while Lean supplies small-kernel rechecking and ecosystem reuse. Covered paths can combine both into a verifiable, reviewable, reusable workflow.

<a id="mathematics-practice"></a>

## From Four Design Principles to Mathematical Practice: Definition and Verification

In formal practice, mathematical work repeatedly moves between two activities. **Definition** introduces objects, relations, and reusable interfaces that give a domain its language. **Verification** establishes what follows from those definitions and the available conditions. The earlier group and algebraic-equality examples were local slices; the full convergence example below puts definitions, quantifiers, witnesses, and estimates into one proof flow.

<a id="convergence-example"></a>

<details>
<summary><strong>Full example: define convergence and verify preservation under scalar multiplication</strong></summary>

Lean's default interaction begins from the final Goal. The user rewrites, decomposes, or closes it with tactics; the system constructs a proof term and submits it to the kernel.

> **Lean tactics: The theorem first presents the final Goal → the user says how it should be rewritten, decomposed, or closed → the Infoview shows which Goals remain → tactics construct a proof term → the kernel checks that term.**

The example defines sequence convergence, then proves that if `{s(n)}` converges to `a`, `{c * s(n)}` converges to `c * a`.

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

This Lean proof is general, abstract, and compositional—an important source of its expressive power. Yet its default direction differs from ordinary writing, and beginners must learn many tactics. Everyday mathematics more often proceeds as follows:

1. Write down the objects, definitions, and conditions.
2. Recognize a familiar pattern.
3. Use a known fact, definition, or computation to write the next fact.
4. Let that fact become part of the context for later reasoning.

Litex makes this workflow its default execution model:

> **Litex: The user states “what should hold” → the verifier searches for proof support → an accepted fact extends the current context.**

The corresponding Litex first defines “eventually close” and “converges to,” then extracts a position from the original convergence statement and constructs a witness for the new sequence:

```litex
# 1. Use prop to define “eventually close”: forall n, n >= N0 leads through =>: to the distance bound.
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            abs(s(n) - a) < epsilon

# 2. Convergence reads: forall positive epsilon, there exists an N0 that makes the prop hold.
prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}

# 3. State “s converges =>: c * s converges” as a thm.
thm converges_to_mul_const:
    ? forall s fn(n N) R, a, c R:
        $converges_to(s, a)
        =>:
            $converges_to(fn(n N) R {c * s(n)}, c * a)
    # 4. First claim the local goal: forall epsilon, prove that an N0 exists.
    claim:
        ? forall epsilon R+:
            exist N0 N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)}
        # 5. To supply that existence witness, choose the smaller positive error epsilon / (abs(c) + 1).
        abs(c) + 1 > 0
        epsilon / (abs(c) + 1) $in R+
        # 6. Original convergence already says such a K exists, so obtain N0 from it.
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / (abs(c) + 1), K)}
        # 7. To finish the new existence claim, offer that same N0 as the witness.
        witness exist K N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, K)} from N0:
            # 8. Enter forall n; put n >= N0 left of =>:, then prove the distance bound on the right.
            forall n N:
                n >= N0
                =>:
                    abs(s(n) - a) < epsilon / (abs(c) + 1)
                    # 9. Follow the fact chain: factor out abs(c), then use abs(c) <= abs(c) + 1 to get below epsilon.
                    abs(c * s(n) - c * a) = abs(c * (s(n) - a)) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < (abs(c) + 1) * (epsilon / (abs(c) + 1)) = epsilon
                    # For the new sequence written with fn, this is exactly the required fact at n.
                    abs(fn(k N) R {c * s(k)}(n) - c * a) < epsilon
            # 10. by def is_eventually_close: by definition, the forall fact above is “eventually close.”
            by def $is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)
    # 11. by def converges_to: by definition, that forall / exist structure is convergence.
    by def $converges_to(fn(n N) R {c * s(n)}, c * a)
```

The first two `prop` declarations establish the domain language: what it means to be eventually close and to converge. Then `obtain N0` extracts a position from the original convergence statement, while `witness` supplies it for the new sequence. Choosing `epsilon / (abs(c) + 1)` avoids a separate `c = 0` case, and the inequality chain compresses the error below `epsilon`. The example combines both kinds of mathematical work: define a reusable interface, then verify a new fact through it. Fact orientation changes the interface; it does not remove the mathematics.

</details>

<a id="interaction-loop"></a>

## The End-to-End Human–AI–Litex Verification Loop

The end-to-end verification loop applies to a single definition, one theorem, a proof repair, a reusable mathematical interface, a textbook chapter, or a multi-file theory. It is not tied to any mathematical subject or example.

The outcome is not merely Litex code. A successful loop produces:

1. a human-owned mathematical contract;
2. a dependency-ordered mathematical development;
3. a JSON record of verifier-backed attempts and decisions;
4. materialized `.lit` source containing only accepted mathematics;
5. an honest verification and trust-boundary report; and
6. when explicitly in scope and supported, a Lean artifact checked by Lean's kernel.

```text
Human fixes mathematical intent, constraints, and acceptance boundary
                              ↓
AI proposes the next Litex fact or proof block
                              ↓
Litex checks well-definedness and proof evidence
       ├─ Committed (reader label: Accepted)
       │      ↓
       │  Accepted context grows → AI proposes the next block ─────↗
       │
       └─ RolledBack (reader label: Stopped)
              ↓
          Context is unchanged
              ↓
      JSON records the failed phase and goal
              ↓
       AI repairs the same block ─────────────────────────↗

Contiguous Committed prefix
              ↓
Materialize .lit → clean Litex gate → trust / boundary audit
              ↓ only when the route is supported and artifacts are generated
Generated.lean → Adapter.lean → Final.lean → Lean kernel
```

<a id="ecosystem-role"></a>

## From Language to Ecosystem: The Role Litex Aims to Play

**Litex serves humans and AI as both a readable-reasoning front end and a production layer for trustworthy reasoning data, connected to existing ecosystems through Lean and Mathlib. It aims to serve AI, engineers, and other domain practitioners as well as formal-methods experts.**

These three roles correspond to the following concrete outputs:

| Ecosystem role | Outputs Litex aims to produce |
| --- | --- |
| Front end for readable reasoning | Mathematical objects, conditions, intermediate facts, and conclusions that people can inspect directly |
| Production layer for trustworthy reasoning data | Machine-checked facts and verification sources, explicit stopping boundaries, and explicitly marked uses of `trust` and other trust boundaries |
| Connection to the existing ecosystem | Lean proof terms for currently supported source routes, plus explicitly separate AI- or human-authored adapters for additional Lean/Mathlib interfaces |

“Trustworthy reasoning data” does not give every output mature-proof-assistant guarantees. It means the data carries checking results, sources, and boundaries. Builtin and infer rules, `trust`, and implementation still require audit; only a route fully compiled and accepted by Lean gains the smaller kernel's additional check. Coverage and adapters are still expanding.

Code and dataset volume are intermediate measures. What matters is whether people understand the artifacts, machines check them, later reasoning reuses them, and supported paths enter existing toolchains. Only those outcomes can turn a language experiment into shared reasoning infrastructure.

<a id="conclusions"></a>

## Conclusion

Litex uses syntax and an interaction contract closer to ordinary mathematics to lower authorship and review barriers, make mathematical text executable, and support deeper understanding and discovery.

Four choices serve one division of labor: set theory keeps objects readable, fact orientation preserves *what holds*, bottom-up flow accumulates verified facts, and Lean compatibility rechecks covered routes. Litex does not replace Lean; it tests whether a smaller, mathematics-facing front end can let more people produce, review, and repair checked mathematics at lower cost.

If formal languages become as routine as LaTeX over the next decade, their entry cost should approach LaTeX's. This is a long-term onboarding standard. It does not imply that deep mathematics, complete formalization, or mastering a proof assistant will become effortless.

**Litex's success will not be measured by how much Litex code is written, but by whether it can turn readable reasoning into useful results that interoperate with existing formal-language systems and genuinely serve mathematics, AI, engineering, and other fields.**

Evaluation should focus on outcomes: can people audit intent; can humans and AI continue from verification feedback; can facts be reused across projects; can supported routes enter Lean/Mathlib; and do real tasks adopt the artifacts? Code, theorem, and dataset counts track progress but cannot establish success alone.

If this direction works, it can lower authorship and review barriers, turn readable text into checked reusable artifacts, and help humans and AI understand mathematical relationships. Deeper understanding and discovery are possible long-term outcomes, not results already secured by language design.

### Related Links

1. To try examples directly and inspect Litex's output and knowledge graphs, visit [litexlang.com](https://litexlang.com).

2. For the kernel implementation, see the [golitex repository](https://github.com/litexlang/golitex).

Note: the repository contains checked results, experiments, and unfinished work side by side. *Publicly visible does not mean claimed complete.* Judge capabilities by current tests, dated status, trusted boundaries, and known limitations.
