# Litex: The Formal Language Where Math Verifies Itself

Created and maintained by Jiachen Shen.

Website: https://litexlang.com/doc/Litex_Blueprint

Chinese version: https://litexlang.com/doc/Litex中文蓝图

> **Litex is an experimental hobby project still in beta. Expect rough edges.**

> **Core positioning.** Litex is a set-theory-based, fact-oriented language
> for readable checked mathematics. Users write the mathematical facts that
> form the proof spine; Litex reconstructs routine local justification through
> fact matching, equality replacement, definitions, quantified rules, and
> bounded mathematical reasoning.

## Table of Contents

- [Background](#background)
- [Starting from the Everyday Mathematical Workflow](#workflow)
- [A Small but Complete Comparison: A Reciprocal with a Restricted Domain](#reciprocal-comparison)
- [How Litex Pursues These Goals](#design-goals)
  1. [Users State Mathematical Patterns and Results; the System Searches for Concrete Proof Support](#goal-1)
  2. [Present Set-Theoretic Objects at the Surface](#goal-2)
  3. [Shape the Syntax Around Mathematical Reasoning](#goal-3)
  4. [Preserve Rigor While Remaining Readable and Accessible](#goal-4)
  5. [Build Proofs Bottom-Up from Verified Facts](#goal-5)
- [Litex: A Concise Mathematical Front-End Language for the Trusted Lean Ecosystem](#compatibility)
- [Conclusions](#conclusions)
- [Appendix A: Why Does Litex Have So Many Builtin Rules?](#appendix-builtins)
- [Appendix B: Why Does Litex Have So Many Examples?](#appendix-examples)
- [Appendix C: What Litex Is Doing About the Conditions for Success](#appendix-conditions)

<a id="background"></a>
## Background

Litex is a formal language for mathematics centered on objects and facts. It aims to lower the barriers to learning, writing, and reviewing formal proofs, so people and AI can express reasoning, enhance understanding, and spark new ideas in a form close to ordinary mathematics. At the same time, every conclusion submitted to the system is subject to rigorous machine checking.

### From Mathematical Notation to Formal Language in the AI Era

Throughout the history of mathematics, important new systems of notation have done more than shorten what people write. They have gradually changed how people see problems, organize reasoning, and explore new directions. The Hindu–Arabic numeral system reshaped calculation. The calculus notation developed and promoted by Leibniz made relationships among rates of change, differentials, and integrals easier to express and manipulate. In the modern era, TeX and LaTeX primarily addressed mathematical typesetting, but their stable, widely shared notation also changed how mathematical knowledge is written, exchanged, published, and reused.

Today, AI is making candidate mathematical proofs far more common and scalable. As proofs cease to be only texts written by hand by a comparatively small number of people, the central bottleneck shifts from “can a plausible-looking argument be generated?” toward “can it be checked, reused, and accumulated reliably?” This makes formal languages increasingly important. Formal expression may gradually become a layer of mathematical infrastructure as indispensable as LaTeX is for typesetting—not only allowing machines to read proofs, but allowing them to check those proofs rigorously.

Litex aims to bring that layer of technology within reach of ordinary learners and users of mathematics. Its ideal is: **if you understand some mathematics, you should be able to express that mathematics in a formal language.** Someone who already understands secondary-school mathematics, for example, should be able to learn quickly how to express the corresponding definitions, reasoning, and proofs in Litex, without first becoming a proof-assistant expert. This remains a design goal to be tested through runnable examples, learning costs, and real use; it is not a promise that the current beta has already achieved it across mathematics.

To understand why this goal calls for a different language design, first consider the relationship between formal proof and the workflow of ordinary mathematical writing.

<a id="workflow"></a>
## Starting from the Everyday Mathematical Workflow

Mainstream formal languages such as Lean have achieved enormous success, providing rigorous checks for formal proofs written by humans and AI. Lean's default interaction begins with the final Goal: the user repeatedly rewrites, decomposes, or closes the current Goal with tactics; the system uses those instructions to construct a proof term, which is then checked by the kernel.

> **Lean tactics: the theorem states the final Goal → the user states how to rewrite, decompose, or close it → Infoview shows which Goals remain → tactics construct the proof term → the kernel checks the term.**

As an example, consider proving directly from the definition of convergence that if a sequence `{s(n)}` converges to a real number `a`, then `{c * s(n)}` converges to the real number `c * a`:

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

This proof mode is highly general, abstract, and compositional, and it is an important source of Lean's expressive power. But its default direction is not quite the same as ordinary mathematical writing, and beginners must also become familiar with a substantial vocabulary of tactic keywords. Ordinary mathematical writing more often proceeds as follows:

1. Write down the objects, definitions, and conditions.
2. Recognize a familiar pattern.
3. Use a known fact, definition, or computation to write the next fact.
4. Add that fact to the context for subsequent reasoning.

Litex turns this everyday workflow into its default execution model. The whole process can be summarized as follows:

> **Litex: the user states what should hold → the checker searches for proof support → the output explains why and how the statement was verified → the verified fact enlarges the context → the proof grows bottom-up.**

Returning to the sequence example, the Litex code reads more like ordinary mathematical writing to a beginner:

```litex
prop is_eventually_close(s fn(n ℕ) ℝ, a ℝ, ε ℝ+, N0 ℕ):
    ∀ n ℕ:
        n ≥ N0
        →:
            abs(s(n) - a) < ε

prop converges_to(s fn(n ℕ) ℝ, a ℝ):
    ∀ ε ℝ+:
        ∃ N0 ℕ st {$is_eventually_close(s, a, ε, N0)}

thm converges_to_mul_const:
    ? ∀ s fn(n ℕ) ℝ, a, c ℝ:
        $converges_to(s, a)
        →:
            $converges_to(fn(n ℕ) ℝ {c * s(n)}, c * a)
    claim:
        ? ∀ ε ℝ+:
            ∃ N0 ℕ st {$is_eventually_close(fn(n ℕ) ℝ {c * s(n)}, c * a, ε, N0)}
        abs(c) + 1 > 0
        ε / (abs(c) + 1) ∈ ℝ+
        obtain N0 from ∃ K ℕ st {$is_eventually_close(s, a, ε / (abs(c) + 1), K)}
        witness ∃ K ℕ st {$is_eventually_close(fn(n ℕ) ℝ {c * s(n)}, c * a, ε, K)} from N0:
            ∀ n ℕ:
                n ≥ N0
                →:
                    abs(s(n) - a) < ε / (abs(c) + 1)
                    abs(c * s(n) - c * a) = abs(c * (s(n) - a)) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) ≤ (abs(c) + 1) * abs(s(n) - a) < (abs(c) + 1) * (ε / (abs(c) + 1)) = ε
                    abs(fn(k ℕ) ℝ {c * s(k)}(n) - c * a) < ε
            by def $is_eventually_close(fn(n ℕ) ℝ {c * s(n)}, c * a, ε, N0)
    by def $converges_to(fn(n ℕ) ℝ {c * s(n)}, c * a)
```

Along these two axes, Litex's default interaction runs in the opposite direction from Lean tactics. Here, “opposite” describes only the direction of the default workflows, not the overall capabilities of the two systems.

1. **Litex grows bottom-up; Lean tactic proofs work top-down.** In Litex, each verified fact extends the context until the accumulated facts support a conclusion. Lean tactic proofs normally begin with the final Goal and work backward, transforming it into new Goals until they can be closed by known facts.

   > Think of writing a proof as building with LEGO. At the outset, we are given a set of available bricks and a completed reference model; the task is to prove that those bricks really can build that model. Lean tactics, by default, are like starting from the target model and taking it apart step by step. The proof succeeds when the pieces obtained at the end match the bricks available to us. Litex, by default, is like picking up the available bricks and assembling them one step at a time until they form a model identical to the completed one. The assembly order is not rigidly prescribed: we may build from different angles and in different orders, as long as we eventually produce the target model. This analogy concerns freedom in step order, not a weaker standard of verification.

2. **Litex users state *what* should hold; Lean tactic users state *how* the Goal should be proved.** The Litex checker searches for matching proof support and explains the route it found. Lean tactic elaboration follows the user's proof instructions to construct the corresponding proof term, the server shows the resulting Goals, and the kernel checks the term.

   > A complete LEGO instruction manual contains two kinds of information: first, how to perform the next step; and second, what the entire partially assembled model should look like after that step. Lean tactic source primarily records the first kind—how to manipulate the proof state next (continuing the previous analogy, it records how we take the model apart at this step). Litex source primarily records the second—what mathematical fact has been established by that step of reasoning (in the same analogy, it records what we have assembled at this step).

These two analogies describe the center of gravity of the default interfaces, not an absolute capability boundary. Lean's mechanism provides a highly flexible and general proof-programming environment. Litex deliberately chooses a narrower default interaction, aiming to make it easier for newcomers to begin a proof while keeping the source closer to ordinary textbook mathematics. Lean also supports forward reasoning, and Litex also provides explicitly goal-directed proof forms. The comparison and five design goals below develop the similarities, differences, and tradeoffs between these two workflows.

> **Comparison note.** Lean remains the running comparison because it makes
> the Goal-first/fact-first contrast especially concrete. References below to
> Mizar, Isabelle/Isar, Rocq, ACL2, and Naproche locate Litex in the existing
> design space: Litex was designed independently rather than derived from
> these systems. The references identify neighboring ideas and the resulting
> differences; they are not claims of direct intellectual influence.

<a id="reciprocal-comparison"></a>
## A Small but Complete Comparison: A Reciprocal with a Restricted Domain

The reciprocal example makes the interface difference concrete without introducing an algebraic hierarchy. The mathematical intention is simple: a positive real is nonzero, so it may be supplied to a reciprocal function whose declared domain excludes zero.

### Lean: Package the Domain Condition in a Subtype

One ordinary Lean formulation makes the restricted domain a subtype. Calling `reciprocal` then requires constructing a new subtype value that packages the real number together with its nonzero proof:

```lean
import Mathlib

def NonzeroReal :=
  {x : ℝ // x ≠ 0}

noncomputable def reciprocal (x : NonzeroReal) : ℝ :=
  1 / x.1

theorem reciprocal_of_positive (a : ℝ) (ha : 0 < a) :
    reciprocal ⟨a, ne_of_gt ha⟩ = 1 / a := by
  rfl
```

Lean and Mathlib also permit an unrestricted `ℝ → ℝ` reciprocal because division is total there. The subtype is chosen deliberately in this comparison: it makes the source-level domain condition visible and shows how a type-oriented interface packages the value and proof before application.

### Litex: Keep the Object and Grow the Required Facts

In Litex, `a` remains the same object. `a ℝ` contributes the membership fact `a ∈ ℝ`; `a > 0` supports the next fact `a ≠ 0`; once that domain fact has been checked, the same `a` can be passed directly to `reciprocal`.

```litex
have fn reciprocal(x ℝ: x ≠ 0) ℝ = 1 / x

∀ a ℝ:
    a > 0
    →:
        a ≠ 0
        reciprocal(a) = 1 / a
```

The Litex runner verifies this snippet without `trust`. It checks the function definition and result set, derives nonzero from the strict order, uses that newly accepted fact to justify the application, and then reduces the named function definition.

The two snippets express the same mathematical move but expose different interfaces. Lean constructs `⟨a, ne_of_gt ha⟩ : NonzeroReal`; Litex retains `a` and accumulates the relations needed to use it. This is not a claim that Lean cannot express membership-oriented mathematics, or that Litex avoids all proof structure. It isolates the default question each surface asks: “which typed value should be constructed?” versus “which facts about this object are now available?”

There is also an important compiler boundary. The Lean block above is ordinary hand-written Lean, not generated output. The current Litex-to-Lean compiler already supports the reciprocal definition and an application whose `a ≠ 0` fact is supplied as a premise in [`12_NamedFunction.lit`](../lean/examples/12_NamedFunction.lit). It does not yet replay the stronger within-theorem path in which the first conclusion `a ≠ 0` supplies the well-definedness evidence for the following application. That exact source remains Litex-checkable while compiler emission fails closed; no `axiom` or `sorry` is inserted.

With this comparison in place, the next five sections explain its design differences and return to the same domain condition from five angles.

<a id="design-goals"></a>
## How Litex Pursues These Goals

<a id="goal-1"></a>
### 1. Users State Mathematical Patterns and Results; the System Searches for Concrete Proof Support

Litex is pattern-first and proof-mechanics-second: source records reusable mathematical structure and the result that should hold, while the checker finds and explains concrete proof support for the current instance. The primary change is not code length but the division of labor between user and system. The user writes results such as `1 + 1 = 2`, the union of finite sets being finite, or `x^2 >= 0`. Litex first checks that the objects in those statements are well-defined, then searches builtin rules, known facts, and known universally quantified facts for support. In typical Lean tactic interaction, the conclusion is first given as a Goal; the user then specifies which facts to invoke and how to rewrite or decompose the Goal, and the system constructs the complete proof accordingly.

A small set theorem makes that division of labor concrete. If `s` is a subset
of `t`, intersecting both with the same set `u` preserves the inclusion. In
Litex, the user can state that result directly:

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

This is a complete fact submitted to the checker, not a proof hole. Its ordinary mathematical reading is enough to describe the argument: take any `x` in `intersect(s, u)`; then `x` belongs to both `s` and `u`. The subset relation carries `x` from `s` to `t`, so `x` belongs to `intersect(t, u)`. The user states the mathematical result to be established; the checker searches for a verification route by unfolding intersection membership, transporting membership through the subset relation, and reassembling membership in the intersection on the right.

The sets chapter of *Mathematics in Lean* gives an explicit unfolding proof:

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

Lean can also express the same proof as a compact, generic proof term:

```lean
example {α : Type*} {s t u : Set α} (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩
```

The Lean versions show explicit control and elegant generality; the latter is even shorter and ranges over every carrier type `α`. The difference is not line count but the default starting point. Litex encourages the user to ask, “What fact should hold next?”, and then state it directly without first learning library names such as `subset_def` or proof-term construction. That default starting point lowers the initial barrier and keeps the source close to ordinary mathematical writing. The tradeoff is that the routine reasoning moves into the Litex checker and must remain tested and auditable.

Generalizing from this example gives the following division of labor:

| Default interaction | User source primarily states | Interactive output primarily supplies |
|---|---|---|
| Lean tactics + server/Infoview | How to rewrite, decompose, or close the current Goal | Which Goals remain after each step |
| Litex facts + checker output | The next fact or result that should hold | Why that fact passed and its immediate verification source |

In short, Lean tactic source emphasizes *how*, while server output supplies *what remains*; Litex source emphasizes *what*, while checker output supplies *why/how*. This describes the center of gravity of the two default interactions, not an exclusive capability boundary: Lean can state intermediate results explicitly, and Litex can organize proofs around explicit Goals.

This division of labor is useful, however, only if the checker can actually recognize these common patterns.

Litex currently encodes hundreds of small, concrete mathematical patterns as builtin verification rules, covering common cases involving numbers, equality, order, sets, functions, tuples, and membership. These rules are not intended to form an invisible “big automation button.” Each rule should have a readable mathematical meaning, an implementation, tests, and a checkable explanation in the output. Litex's precise rule catalog will evolve, so the number of rules is not treated here as a stable headline metric.

Providing a corresponding Lean theorem or code explanation for every builtin rule is a valuable audit target, but a rule should not be treated as formally justified merely because it looks intuitive. The trusted boundary, rule implementations, regression tests, and independent cross-checking all need to remain visible and continue to improve.

Why these rules should be organized around patterns becomes clearer from the habits of ordinary mathematical reasoning.

When doing mathematics, people often begin by recognizing a pattern: the current expression is the same as an earlier one, or differs only by substitution, unfolding, or instantiation. Mathematical reasoning is rarely driven primarily by remembering the internal name of every auxiliary lemma.

Litex therefore places verified facts in the current context and tries to match and substitute them. A known `forall` fact can be instantiated when its parameter conditions are satisfied, and a known equality can help match a larger expression. This is not “guessing a proof”: every accepted result must still pass the rule and context checks. Litex retains named theorems and explicit `by thm` invocations when a result is large, when checking it would be expensive, or when its dependencies should remain visible to the reader.

#### What the “Automatic Verification Magic” Actually Does

The short answer is: a sophisticated, bounded matching-and-replacement
engine. When a user submits a fact, Litex does not send it to an unconstrained
prover and ask for an arbitrary proof. The exact dispatch depends on the shape
of the fact, but the ordinary verification process can be understood as the
following cascade:

1. **Check meaning first.** Verify that the objects, function applications,
   memberships, binders, and other components of the submitted fact are
   well-defined.
2. **Retrieve plausible local support.** Use the fact's relation or predicate
   head and the shapes of its arguments to narrow the search among known
   facts, known `forall` facts, definitions, and builtin rule schemas.
3. **Match the conclusion and bind its variables.** Compare a candidate
   conclusion structurally with the submitted fact. A pattern variable such
   as `a` may thereby be bound to a concrete object such as `identity`; a
   repeated variable must match the same object each time.
4. **Instantiate and discharge the requirements.** Apply those bindings to
   the candidate's parameter types, domain conditions, and premises, then
   verify the resulting concrete requirements through the checks permitted by
   that route.
5. **Bridge small representational gaps.** Where the two shapes are not
   literally identical, try controlled operations such as reversing an
   equality, transporting through known equalities, direct computation,
   bounded symbolic normalization, structural congruence, or a checked
   checked definition reduction.
6. **Commit the result with evidence.** If one bounded route succeeds, record
   its immediate provenance, store the new fact in the context, and apply the
   relevant inference rules. If none succeeds, report `unknown` rather than
   silently inventing a proof.

The important point is that this cascade has more than one source of reusable
patterns. A pattern may come from the builtin rule catalog, or it may come
from a `forall` fact that the user has already proved and placed in the
environment. Their provenance is different, but the central operation is the
same: match the requested conclusion, select a substitution, and check the
instantiated requirements.

First consider a small builtin example:

```litex
forall y R:
    0 <= abs(y + 1)
```

The catalog contains the schema `forall x R: 0 <= abs(x)`. For the atomic
conclusion `0 <= abs(y + 1)`, structural matching selects `x := y + 1`; the
checker then confirms the instantiated requirement `y + 1 $in R` from the
typed binder and the arithmetic rules. The detailed output names the selected
catalog entry, `order.abs_nonnegative`, and exposes its subgoal rather than
hiding the match behind a generic automation label.

Now let the reusable pattern be proved by the user instead:

```litex
thm abs_zero_or_one:
    ? forall x R:
        x = 0 or x = 1
        =>:
            abs(x) <= 1
    by cases:
        ? abs(x) <= 1
        case x = 0:
            abs(x) <= 1
        case x = 1:
            abs(x) <= 1

abs(1) <= 1
# Or explicitly: by thm abs_zero_or_one(1)
```

The theorem is checked once and its `forall` fact is stored. The active line
contains only the atomic fact `abs(1) <= 1`, with no `claim` wrapper and no
required `by thm` call. The following comment shows the alternative for a user
who wants to name the dependency explicitly: `by thm abs_zero_or_one(1)`.
The fact has the same structural shape as the stored conclusion `abs(x) <= 1`:
matching selects `x := 1`, after which the instantiated type and premise are
checkable.

There is one provenance nuance in this deliberately concrete example.
`abs(1) <= 1` is also directly computable, so the current checker reaches the
builtin `number comparison` route before it needs the stored `forall`. The
universal fact is a matching source, but it is not the immediate source
selected in this particular run. This is an example of overlapping local
justifications, not evidence that the checker recorded `cite forall fact` for
this line. The commented `by thm` alternative, by contrast, explicitly selects
the named theorem.

Thus builtin rules and user-proved universal facts are not two unrelated
automation mechanisms. They feed the same bounded match–substitute–check
architecture, while remaining distinguishable in the evidence: one cites a
builtin rule, and the other cites a previously proved fact. Domain-conditioned
functions scale up the same idea: in the reciprocal example, strict order
supports nonzero, and that accepted fact then satisfies the function's call
requirement. The verification principle remains local fact matching even
though the later expression is well-defined only after the earlier fact.

The apparent magic is therefore mostly careful engineering around candidate
indexing, canonical structural matching, equality-aware replacement, bounded
mathematical rules, and provenance. It is more capable than literal string
matching, but much more constrained and auditable than unrestricted proof
search.

#### Hiding Mechanical Proof Work While Preserving the Mathematical Spine

A limited analogy can be made with the successive abstraction layers of
programming languages. C usually frees programmers from arranging individual
assembly instructions; higher-level languages such as Python absorb still more
routine work, including much manual memory management and the requirement to
declare most variable types in advance. Litex is not implemented like either
language, and the analogy does not imply that mathematical types disappear.
What Litex borrows is only the broader design idea: recurring, mechanically
classifiable work can be moved into the language system so that users can work
with the distinctions that matter at their current level.

In this limited sense, Litex's catalog of hundreds of common builtin schemas,
together with shape-directed matching and replacement, aims to act as an
abstraction layer for routine proof plumbing. Conceptually—not as a literal
description of every implementation data structure—one can picture it as a
large, curated dispatch tree: common fact shapes have been classified in
advance, and the checker tries the relevant bounded routes. The practical hope
is that users need not repeatedly name elementary helper lemmas, choose routine
rewrite directions, instantiate obvious parameters, or restate type and
well-definedness consequences when those operations contribute little to the
mathematical move being expressed. The source can instead emphasize
definitions, substantive assumptions, key intermediate facts, and conclusions.

This is a design goal whose boundary still needs to be tested, not a claim that
Litex has already hidden exactly the right things. Work hidden from the source
does not disappear: builtin rules enlarge the trusted surface and still require
implementation review, tests, and independent audit; checker output should
continue to expose the selected provenance; and users can still write an
explicit route such as `by thm` when that dependency matters. The intended
simplification is to move routine work into the checker without moving rigor
out of the system.

#### Verification at the Level Where Mathematics Is Written

Much of working mathematics proceeds by using established facts at the
current level of abstraction. The reciprocal example stays at that level:
`a > 0` supports `a ≠ 0`, and the named function definition supports
`reciprocal(a) = 1 / a`. On its ordinary verification path, Litex does not
first require the user to construct a subtype term. It tries the relevant fact
instances, definitions, replacements, and bounded mathematical rules directly.

This differs from Lean's acceptance path, even though Lean source can also be
high-level. Lean elaboration translates user-facing syntax and tactic results
into [terms in its core type
theory](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/),
and the kernel checks those terms. Lean core terms can retain defined and
opaque constants, so this does not mean that Lean fully unfolds the entire
history of every mathematical concept on each use. The narrower contrast is
that routine Litex verification can finish once a trusted high-level route has
accepted the fact, without first materializing a complete kernel proof term
for that instance.

The resulting performance hypothesis concerns *foundational depth*, not
constant-time verification. Litex is intended to make routine interactive
cost track the breadth of the local proof neighborhood—the number, size, and
ambiguity of relevant facts and rules—more than the fact's distance from the
foundations. Search branching, context size, expression size, computation,
and recursive rule premises can still make verification expensive. Whether
this architecture yields a substantial speed advantage over Lean for a given
class of mathematics is therefore a benchmark question, not a conclusion
established by the language design alone.

In the compiler's design model, every successful verification corresponds to a recursively structured proof route that should, in principle, be recordable in full. The Litex-to-Lean compiler aims to translate that route into a Lean proof term and submit it to the Lean kernel for an independent check.

<details>
<summary><strong>Further reading: How the Litex-to-Lean compiler works</strong></summary>

*This section expands on the implementation and its current correctness boundary. Skipping it does not affect the discussion that follows.*

From a compiler perspective, the evidence selected by the checker for the successful verification of a Litex fact forms a recursively expandable proof tree. Citation of known facts, introduction of `forall` parameters and premises, equality substitution, definition unfolding, computation, and builtin rules form concrete steps in that tree, and any one step may itself branch further. The Litex-to-Lean compiler is not intended to reread the source after verification and “guess” a collection of tactics. Instead, it records the verification route already found by the checker, lowers each supported node to a Lean proof term—sometimes expressed as several tactics—and submits the result to the Lean kernel for an independent check. For example, the persistent compiler ledger contains this membership-transport example:

```litex
sketch:
    have A set = R
    have B set = C
    forall a A, b B:
        a = b
        =>:
            b $in A
            a $in B
```

For this currently supported route, the core of the generated file is shown below. The complete same-name output is checked in as [`lean/examples/1_SetSystem.lean`](../lean/examples/1_SetSystem.lean):

```lean
import Litex

set_option linter.style.nameCheck false

namespace __Compiler_1_SetSystem
namespace __Sketch01

abbrev A : Litex.Set := Litex.R
abbrev B : Litex.Set := Litex.C

theorem __fact0 :
    ∀ (a : ℂ) (__h0_1 : Litex.In a A)
      (b : ℂ) (__h0_2 : Litex.In b B)
      (__h0_3 : Litex.Same a b),
      Litex.In b A ∧ Litex.In a B := by
  intro a __h0_1 b __h0_2 __h0_3
  exact ⟨(Litex.In.congr __h0_3 A).mp __h0_1,
    (Litex.In.congr __h0_3 B).mpr __h0_2⟩

end __Sketch01
end __Compiler_1_SetSystem
```

This Lean code exposes the new semantic wrapper directly. Generated files uniformly `import Litex`, the public umbrella for the core and its proved rules; Litex values are no longer compressed into a custom universal `Litex.Object` type. The source definitions `A = R` and `B = C` become `Litex.Set` values. Each `Litex.Set` stores the set's exact Lean carrier: `R` uses `ℝ` and `C` uses `ℂ`, rather than simulating a source set with `Set.univ` over an ambient type. In the current numeric slice, the source variables are ordinary Lean values `(a b : ℂ)`. Whether they belong to a Litex set is expressed by separate evidence, `Litex.In a A` and `Litex.In b B`; Lean typing does not replace source membership. The source equality `a = b` becomes heterogeneous semantic equality, `Litex.Same a b`. The two applications of `Litex.In.congr` then transport the retained membership facts strictly along that `Same` evidence, without a cast, implicit axiom, or new proof hole.

The source `sketch` becomes a Lean namespace rather than an extra logical wrapper. `__fact0` corresponds to the persistent fact's verifier-owned `FactId`; its three `__h...` arguments retain the two domain-membership facts and the equality premise in source order. The proof IR records the `forall` introduction, these exact fact identities, and the proof nodes used for membership transport. The compiler is therefore not guessing a convenient Lean tactic after the fact; it is explicitly re-expressing the verification evidence already selected by the checker as a Lean proof.

Known-`forall` use is expanded in the same style. The IR retains every source object selected for a binder, the exact `Litex.In` or other domain evidence it satisfies, every proposition-valued premise, and the conclusion obtained by direct substitution; it does not repack those objects into a universal object universe. Lean materializes the selected ordinary Lean values as local names such as `proof_arg_2_1`, replays proposition-valued premises as `proof_fact` values, and names the direct theorem application. If that direct instance is only rationally equal to the requested spelling of the goal, an enclosing normalization node names the final result separately and checks the conversion. Thus an application is not compressed into a single opaque-looking `factN ...` line, and a matcher-level equality is not silently treated as definitional equality by Lean.

For existential statements, the same principle now has a concrete implementation. A positive `witness exist` retains its concrete witnesses, type checks, local proof steps, and direct body proofs; `obtain` and body-style `have` retain the alpha-checked source existential and each exact stored projection. Lean receives a nested `Exists` proof followed by ordered `Exists.choose`/`choose_spec` terms, including multiple witnesses and proof-local extraction. `exist!`, `not exist`, and preimage extraction remain separate boundaries rather than being approximated by this node.

For builtin rules, known-`forall` instantiation, computation, and deeper composite proofs, the proof IR should likewise retain the corresponding evidence and branches recursively. Litex provides rich automatic verification routes for common mathematical objects; once a successful route has been selected, each step has explicit support and should be recordable and replayable. The current Litex-to-Lean MVP covers only some of these routes. When the compiler encounters a rule that it does not yet support, it stops that compilation instead of degrading into an implicit `axiom`, a `sorry`, or something presented as proved. Therefore, “every Litex verification can be compiled to Lean and accepted by the Lean kernel” remains a correctness goal rather than a completed fact. Once the compilation coverage is sufficiently complete, the translation preserves semantics, and the compiler itself has been audited, this path can provide a strong independent correctness guarantee for Litex verification results.

> **Current boundary:** The Litex-to-Lean compiler remains under design and implementation and has not yet been tested at scale. As later Litex versions revise the kernel and compiler, the Lean code generated from the same Litex example may change. Discussion and collaboration are welcome.

</details>

In the reciprocal example, the source states `a ≠ 0` and then
`reciprocal(a) = 1 / a`. The checker supplies two different local reasons: a
strict-order rule for the first fact and the named function definition for the
second. The source records what should hold, while the verification route
records why each line is available.

> **Position in the design space.** Local support search is not unique to Litex:
> [Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/),
> [Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html),
> and [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) expose it
> through explicit tactics or proof methods;
> [Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf) has empty
> justifications; [ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM)
> can attempt theorem events without hints; and
> [Naproche](https://naproche.github.io/) checks controlled-natural-language
> proof steps with automated theorem provers. Litex's narrower hypothesis is
> that bounded, fact-triggered local justification can be the ordinary default
> semantics of mathematical statements, with accepted facts committed back to
> the context and their provenance exposed.

<a id="goal-2"></a>
### 2. Present Set-Theoretic Objects at the Surface Instead of Requiring Users to Learn Type Universes First

Once the division of labor between the user and the checker is clear, the next question is what kinds of mathematical objects users encounter directly in the source.

The Litex surface language presents objects, sets, membership, functions, and structures as ordinary mathematical objects: objects belong to sets; structures are subsets of Cartesian products with named views; and properties are expressed by predicates. The phrase `s set` states the mathematical judgment that “`s` is a set.” It does not add another user-facing layer of `Type`, universes, or proof terms that must be operated explicitly.

This does not mean that the language imposes no constraints. In the current implementation, function domains, result sets, structure fields, and set membership are still checked; these constraints are simply written where mathematicians would normally write them. Litex also retains parameterized constructions such as `template`, because ordinary mathematics genuinely needs families of objects indexed by carriers, parameters, or assumptions. Litex does not present itself as a complete dependent type theory.

The reciprocal example makes this surface concrete. `a ℝ` contributes
membership in the real set, while `a ≠ 0` is a separate applicability fact.
Litex does not replace `a` with a newly packaged “nonzero real” object before
the call; the original object remains available with both relations attached
to it.

> **Position in the design space.** A set-theoretic presentation is not a Litex
> novelty: [Mizar's library](https://wiki.mizar.org/library/) is based on
> Tarski–Grothendieck set theory, while
> [Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) and
> [Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html)
> expose dependent type-theoretic cores, and
> [Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
> uses polymorphic higher-order logic. Litex's question is specifically about
> the user-facing object interface: can a small, membership-centered,
> set-theoretic surface cover substantial mathematics without requiring users
> to manage type universes first?

<a id="goal-3"></a>
### 3. Shape the Syntax Around Mathematical Reasoning, Not Functional Programming

Once the surface representation of the objects has been established, the next question is how the proof itself should unfold in the language.

A Litex file has only a few core kinds of action: define an object or concept, check a fact, check that an object is well-defined, and provide a witness, case split, or induction when needed. In the common sequential style, users can write in textbook order: a definition, conditions, a local conclusion, the next local conclusion, and a theorem.

This does not mean that Litex never needs structured proofs. Existence, contradiction, case analysis, and induction still require the corresponding mathematical moves to be stated explicitly. Routine computation, substitution, and use of known laws, however, need not be decomposed into a pipeline of “set a goal, invoke a tactic, name an intermediate result, invoke another tactic.” The language should not force users to reorder a clear mathematical narrative merely to follow the construction order of a functional proof term.

In the reciprocal example, the file follows the ordinary mathematical order:
define the restricted function, assume positivity, state nonzero, and apply
the function. The source does not interrupt that sequence with a constructor
such as `⟨a, ne_of_gt ha⟩`; the domain evidence stays visible as the
mathematical fact `a ≠ 0`.

> **Position in the design space.** Readable, declarative mathematical syntax also
> has important predecessors: Mizar organizes formal articles as sequences of
> mathematical statements and justifications, Isabelle/Isar provides
> structured declarative proofs, and Naproche checks controlled natural
> language. Litex's more specific bet is that one compact object–fact syntax
> can let a meaningful mathematical statement double as its routine
> verification request.

#### A Larger Comparison: Defining and Using a Group

The reciprocal example isolates one function and one domain condition. Litex
also needs to scale to mathematical objects that package a carrier, several
operations, and reusable laws. The following comparison proves that any right
identity in a group is the group's distinguished identity.

One ordinary Lean formulation makes the carrier and laws explicit in a local
record. The namespace only avoids a name collision with Mathlib's existing
`Group` class:

```lean
import Mathlib

namespace GroupIdentityExample

structure Group where
  Carrier : Type
  mul : Carrier → Carrier → Carrier
  one : Carrier
  inv : Carrier → Carrier
  mul_assoc : ∀ a b c : Carrier, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : Carrier, mul one a = a
  mul_one : ∀ a : Carrier, mul a one = a
  mul_left_inv : ∀ a : Carrier, mul (inv a) a = one

theorem right_identity_unique
    (G : Group)
    (e : G.Carrier)
    (hright : ∀ a : G.Carrier, G.mul a e = a) :
    e = G.one := by
  calc
    e = G.mul G.one e := (G.one_mul e).symm
    _ = G.one := hright G.one

end GroupIdentityExample
```

The corresponding Litex code defines the same kind of structured interface
over a set carrier. `struct` packages the operations and laws; a later fact
receives `G &Group<s>` and can use those laws without expanding how the
structure is represented:

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
        G.mul(a, identity) = a
    =>:
        identity = G.mul(G.one, identity) = G.one
```

The Lean proof names the two equality steps in a `calc` block. The Litex
conclusion states the same chain directly: the stored group law gives
`identity = G.mul(G.one, identity)`, and the assumed right-identity fact gives
`G.mul(G.one, identity) = G.one`. This is a secondary capacity comparison,
not a second running example for the rest of the blueprint: the smaller
reciprocal example remains the main interface comparison.

Both blocks are hand-written representations of the same mathematics. The
Lean block is not generated compiler output, and this example does not claim
that the current Litex-to-Lean compiler supports `struct Group`.

<a id="goal-4"></a>
### 4. Preserve Rigor While Remaining Readable and Accessible

A more natural surface for objects and proofs matters only if it does not weaken rigor.

A textbook-like surface does not lower the standard of checking. In the current checking process, every submitted fact receives one of `true`, `unknown`, or `error`. The process distinguishes whether an expression is well-defined, whether the current context is sufficient, and which builtin rule, known fact, or universally quantified fact supports the conclusion. A `trust` statement remains an explicitly injected assumption rather than a proof, and builtin and inference rules remain part of the trusted computing base.

Litex is therefore not a replacement for Lean, Coq, or Isabelle. It currently tests a complementary interface: can a smaller, readable, fact-oriented, set-theoretic surface make it inexpensive enough for students, domain researchers, and AI agents to produce, check, and repair useful formal mathematical data? Whether this interface experiment succeeds must be demonstrated through runnable examples, recorded failures, tests, rule audits, and independent checking—not by how natural the syntax appears.

The reciprocal snippet passes only after the runner checks the function body
and result set, real membership, strict order, the derived nonzero fact, the
application's domain requirement, and the final equality. It contains no
`trust`; any such statement would instead be an explicit addition to the
trusted boundary, alongside the checker and its builtin and inference rules.

The intended fast path and this trusted boundary are two sides of the same
choice. Litex can stop after a high-level verification route is accepted
because the implementations of the rules on that route are trusted. Lowering
the recorded route into a Lean proof term and checking it with the Lean kernel
reintroduces a slower but more independent audit path. This architecture makes
low-latency local checking plausible; it does not by itself establish that
current Litex is universally faster.

> **Position in the design space.**
> [Lean](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
> and [Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html)
> sharply separate sophisticated proof construction from kernels that check
> the resulting terms. Litex currently places many mathematical builtin and
> inference rules inside its trusted boundary, so readability alone is not a
> correctness argument. Recorded proof routes, rule audits, regression tests,
> and the Litex-to-Lean path are how this interface can seek stronger
> independent checking.

<a id="goal-5"></a>
### 5. Build Proofs Bottom-Up from Verified Facts

The first four goals have explained how the user and checker divide the work, what objects the user sees, how proofs are expressed, and how rigor is maintained. The final goal turns to how a proof grows forward with its context.

Litex is fact-oriented. Its default unit of progress is the next mathematical fact, rather than an active Goal that every line must immediately advance. If a statement is in scope, well-defined, and justified by the current context, the checker can accept it, store it, apply any currently applicable inference rules, and expose the enlarged context to later statements. A typical Litex proof therefore grows forward and bottom-up: establish facts, derive further facts, and continue until the accumulated context supports the final conclusion. A fact may be used by the next line, by a theorem much later, or may remain an independent checked result. Several branches of a mathematical development can grow separately before a later statement makes them converge.

Lean's ordinary interactive theorem proving is goal-directed and typically works backward or top-down. The final theorem first determines the expected type. Local terms and tactics are elaborated under that expectation, progressively decomposing the pending Goal into simpler subgoals until Lean can assemble the complete proof term. The contrast can be stated as two default questions: Lean asks, “What must still be proved to construct this Goal?” Litex asks, “What fact follows next from the context already established?”

This is a difference in default workflow, not an absolute expressive boundary. Lean can accumulate forward facts with `have`, local lemmas, and independent top-level theorems; Litex can organize explicitly goal-directed work with forms such as `claim` and `thm`. These interfaces primarily change the direction of development, not the standard of correctness: scope, well-definedness, and mathematical justification remain mandatory for every accepted Litex fact.

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

The corresponding Litex proof reverses Lean's four Goal transformations into one equality chain. The chain starts from the right-hand side of the Goal, `c * (d * f)`, states the intermediate results in turn, and ends at the left-hand side, `a * (b * g)`:

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

The user therefore does not have to recall a library identifier such as `mul_assoc` or explicitly orchestrate the order and direction in which `h`, `h'`, and associativity are used. Instead, the user writes a mathematically meaningful chain of intermediate results. If one equality step spans too much reasoning, the added guidance is another intermediate expression rather than a step-by-step search instruction. This example deliberately avoids automation that could normalize the whole algebraic goal at once: the point is to compare the default direction of interaction, not code length.

The preceding example concerns algebraic rewriting. To show that the contrast does not depend on computation, consider another example that transports membership along set inclusions. Lean starts from the Goal `x ∈ c` and uses `apply` to state, step by step, how it should be proved:

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
the Litex source. Only the fields directly relevant to the two conclusions are shown
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

To see more clearly how source and output complement each other, expand Lean's Infoview interaction. The Lean source does not state its intermediate Goals as mathematical results inside the theorem. As the cursor moves forward through the tactics, Infoview supplies that missing part. The local context, which is unchanged at each step, is omitted below:

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

The runner trace and Infoview therefore supply exactly what their respective sources leave
unstated. The Litex source already contains `x $in B` and `x $in c`, so the
runner reports why they passed. The Lean source states how to manipulate the
proof state, so Infoview reports which Goal remains after each step.

Together, the two examples make “bottom-up” concrete. Lean begins with a complete Goal and rewrites or decomposes it until it reaches known facts. Litex establishes checkable equalities or membership facts until they support the final conclusion. Ordinary mathematical writing often works similarly: definitions, known facts, and decisive intermediate results are recorded first and then converge on a conclusion, rather than always decomposing a formal Goal backward into subgoals. For both people and AI systems, proposing meaningful intermediate expressions is often more natural than continually remembering library identifiers such as `pow_two` and `mul_assoc` together with their invocation directions. This common tendency does not mean that every mathematical discovery or proof is strictly bottom-up: induction, contradiction, existence proofs, and complex theorems may still need an explicit goal structure.

Returning to `reciprocal`, its definition is verified and stored first. Inside
the later universal fact, positivity supports nonzero; only after that fact is
accepted is the restricted application checked. This is the same bottom-up
pattern illustrated by the calculation and inclusion examples, compressed
into a function call whose well-definedness visibly depends on context growth.

> **Position in the design space.** Mizar and Isar already support forward,
> declarative proof text; ACL2 grows a reusable theorem database; and Naproche
> checks successive mathematical steps. Bottom-up growth alone is therefore
> not the claim. Litex tests the combination in which an ordinary fact is the
> context-growing executable unit, local justification begins without a
> separate method invocation, and explicit proof structure appears when
> routine reconstruction reaches its boundary.

<a id="compatibility"></a>
## Litex: A Concise Mathematical Front-End Language for the Trusted Lean Ecosystem

Litex is first of all a formal language that works in its own right. It has its own syntax, runtime, and checker. A Litex mathematical document can undergo Litex's well-definedness checks, fact verification, and local proof feedback without ever being compiled to Lean. Calling Litex a “mathematical front-end language for Lean” therefore does not mean that it is merely syntactic sugar embedded in Lean or that it depends on Lean in order to run. It means that Litex can additionally compile mathematics it has verified into Lean, allowing an independent source language to connect to Lean's trusted kernel, the Mathlib library, and the wider Lean toolchain.

> **Ideally, as Litex-to-Lean compilation matures, definitions, theorems, and proofs written in Litex can be carried faithfully into Lean and checked there independently, without filling gaps with additional axioms. Choosing Litex would therefore not mean leaving Lean. Mathematics completed in Litex could still enter Lean and Mathlib, where it can be checked, cited, and developed further. Even if your goal is to contribute to the Lean community, you can first use Litex to help express and advance your mathematics: Litex and Lean need not compete for your time; they can carry the same mathematical work together.**

Lean and Mathlib have already established a powerful foundation for formal mathematics. Litex does not seek to duplicate or replace these achievements; it aims to combine its independent language experience with this mature infrastructure.

When using Litex, users can concentrate on mathematical objects, conditions, intermediate facts, and conclusions while receiving fast, local, and traceable feedback from the checker. This matters for AI systems as well. A generative system can propose the next mathematical fact in small steps and then revise it in response to the checker's concrete support or failure boundary, without first reducing the entire mathematical intention to the details of elaboration, typeclasses, namespaces, and tactic invocation. Those mechanisms are important sources of Lean's expressive power and compositionality. Litex does not reject them; it asks whether they must be the first threshold that every new participant crosses on the way into formal mathematics.

*Litex-to-Lean Compiler also provides an important independent foundation for confidence in Litex's rigor.*

The Rust source under Litex's `src/` directory alone currently exceeds 210,000 lines and continues to grow with hundreds of builtin and inference rules and other capabilities. Auditing such a large trusted implementation surface is naturally much harder than auditing Lean's far smaller kernel. When a Litex verification route can be compiled in full into a Lean proof and accepted by the Lean kernel, that acceptance provides strong, independent correctness evidence for the covered route and substantially reduces sole reliance on Litex's own large implementation.

This makes Litex more than a shorter syntax; it offers a different interaction contract. People and AI systems primarily express *what holds* mathematically, the Litex checker records *why it holds*, and the compiler must preserve the actual verification route, scope, fact citations, well-definedness dependencies, and sources of `trust` before the Lean kernel checks the exported proof.

> **Litex aims to bring the entrance to formal mathematics closer to mathematics itself, while allowing its results to flow into Lean's trusted kernel and broad ecosystem. Even a ten-year-old doing mathematics should be able to begin with Litex and experience the appeal and power of formal languages.**

_This remains a goal that Litex is implementing and testing, not a capability that the current beta has already achieved in full. The general idea and implementation framework is established, but implementation details need refinement. I welcome feedback from the community as we work to improve Litex._

<a id="conclusions"></a>
## Conclusions

Litex should not promise to “omit proof.” Its intended promise is both stricter and more modest: let users first write the mathematical facts they actually mean, then let the machine expose the verification, provenance, and boundaries clearly.

That design thesis creates four layers of potential value:

1. **Lower the cost of checked formalization.** By letting authors record the mathematical proof spine while the checker reconstructs routine local connections, Litex aims to make more mathematics economical to formalize. The decisive metric is total effort on the same real tasks, not source-code length alone.
2. **Provide a verification interface for human–AI collaboration.** A person or AI system can propose the next mathematical fact, receive local machine-checkable feedback, and repair the exact boundary that failed; accepted facts and repair traces can then become reusable formal data rather than merely plausible text. This value depends on the verdicts and their provenance being trustworthy.
3. **Make mathematical texts executable.** Definitions, lemmas, and proofs can remain readable as mathematical exposition while also being checked and reused across files and chapters. This could bring formal verification closer to textbooks, teaching, and scientific writing instead of confining it to specialist proof-assistant projects.
4. **Turn failed formalization into research evidence.** A precise failure can expose a missing language feature, library fact, inference route, kernel capability, diagnostic, or mathematical formulation. That evidence is valuable only when failures and trusted gaps are recorded rather than concealed.

These values are conditional, not consequences of readable syntax alone. [Appendix C](#appendix-conditions) summarizes the concrete work Litex has begun on the conditions required for them to hold, together with the boundaries that remain open.

In operational terms, that promise has a precise meaning:

> **In Litex, local justification is not a tactic that users invoke; it is the
> default operational meaning of an ordinary mathematical fact.**

When a user writes a bare fact, that line serves two roles at once: it is the
mathematical statement the author wants to retain, and it is a request for the
checker to reconstruct routine support from the current checked context. That
double role unfolds into one complete cycle:

1. **At the surface,** an ordinary fact triggers verification without first
   requiring a named tactic, theorem citation, or proof term.
2. **Inside the checker,** relevant known facts, equalities, definitions, and
   applicable universal facts are considered through bounded,
   mathematics-aware routes.
3. **On success,** the fact and its ordinary inferred consequences immediately
   enlarge the context for what follows.
4. **In the output,** the checker can expose the concrete route and provenance
   that the concise source leaves implicit.
5. **At the boundary of routine reconstruction,** explicit mathematical
   processes such as witnesses, cases, contradiction, induction, and named
   routes remain available.

Read together, these are not five independent conveniences. They define one
default division of labor: the author supplies the mathematical proof spine;
the checker supplies its routine local connections; and explicit proof
structure appears when the mathematics actually demands it.

Seen as language design, this is an abstraction-layer hypothesis still to be
tested: as higher-level programming languages absorb recurring low-level
operations, Litex tries to make repeatable, classifiable proof operations part
of the checker's infrastructure so that source can remain closer to the level
at which mathematical reasoning occurs. That division of labor—not local
automation in isolation—is the intended interface distinction.
The design-space comparisons above show that the individual mechanisms have
precedents. Litex therefore advances a narrower, more architectural
hypothesis: can the entire fact-triggered cycle—not merely an optional tactic,
a citation convention, or a theorem-level prover—serve as the uniform default
semantics of a small object-and-fact language across substantial, readable
mathematics?

The same division of labor suggests a two-path validation architecture. The
routine interactive path can preserve the abstraction level of the submitted
fact and pay primarily for its local proof neighborhood; a separate audit path
can lower the recorded route into a foundational proof term for independent
checking. The first path is an architectural performance hypothesis, not yet
a benchmark-backed claim of universal speed superiority.

Seen this way, the contrast with the familiar Lean tactic workflow is not
automation versus no automation. It is where automation sits in the default
source contract: a Lean tactic proof states a Goal and invokes a proof method;
an ordinary Litex fact triggers routine local justification without a separate
invocation. That difference in the division of labor can be put more sharply.

> **Put sharply: the familiar Lean tactic workflow can feel like being forced to read a mathematics book from its last page, or to write a paper from its last page—first fix the final Goal, then work backward to reconstruct everything that must come before it.**

For mathematical exploration, learning, and textbook-style exposition, this order can feel deeply unnatural to some readers. Litex makes a deliberate design judgment that this backward, Goal-first order should not be the only or default way to write formal mathematics.

When Litex moves concrete proof operations into the checker, however, the pressure shifts to its own trusted boundary.

> **Equally sharply: From a first-principles perspective, Litex's biggest current problem is that its trusted kernel is too large. Litex moves hundreds of common proof patterns into builtin and inference rules, shifting work from the user's proof script into the trusted computing base. The proof work did not disappear; the system absorbed it. For Lean to provide an independent correctness guarantee, Litex must compile its recorded verification routes into Lean proof terms and have Lean check them.**

*I am working on the Litex to Lean compiler. I welcome serious discussions through https://github.com/litexlang/golitex or litexlang@outlook.com.*

For this reason, Litex needs to accumulate experience toward a compilation path to Lean. The current repository has a deliberately partial compiler: it retains stable fact identities and recursive proof evidence, supports a selected object and builtin-rule subset, and now preserves the declaration and temporary-premise scopes of explicit-value `have`, checked bare selection such as `have x R`, positive `witness exist` plus `obtain`/body-style existential extraction, binary `by cases`, atomic `by contra`, source-named theorems, checked named-function definitions, set builders, and one tuple-construction recipe. Selection and extraction consume the verifier's exact existential certificates through Lean's `Exists.choose` and `choose_spec`; they do not become invented opaque constants. Unsupported verified statements are reported and omitted transactionally instead of becoming `sorry` or implicit axioms. It is still far from a compiler for general Litex statements or builtin rules. The long-term target remains to check source with Litex, generate an equivalent Lean statement and proof, and have Lean check that result independently.

The compilation target above addresses trust without giving up the interface
choice. A mature path would let Litex users continue to state *what* should
hold and let the checker reconstruct the local route, while an exported Lean
proof term independently replays and checks that route. The interface thesis
and the trust strategy therefore belong together: local justification can
remain implicit in the source only if the work it absorbs remains inspectable
and becomes increasingly replayable outside Litex's present trusted boundary.

As collaboration between humans and AI gradually creates and accumulates more
mathematical knowledge, formal systems should explore more
than one way to write and verify that knowledge. At the level of their default
interaction directions, Litex can in a limited sense be viewed as “the opposite
of Lean”: Lean tactics typically begin from a final Goal and ask the user how to
construct its proof, while Litex typically begins from established facts and
asks the user what should follow next, leaving the checker to find and explain
the support. This design direction is not an attempt to replace Lean. Instead,
it offers another direction for how humans and AI might write formal mathematics
together—a direction worth practicing and testing.

Because this design direction is still being explored as a research project, the current repository should also be understood as open research in progress:

> At the current research stage, Litex is developed in public, so the repository intentionally exposes experiments and unfinished work as well as checked results. Public availability is not a completion claim; each claim should be read against its current tests, dated status, trust boundary, and known limitations.

<a id="appendix-builtins"></a>
## Appendix A: Why Does Litex Have So Many Builtin Rules?

Litex includes many builtin rules partly to cover the basic behavior of common mathematical objects—numbers, sets, equality, order, functions, and structures—and partly as a deliberate product choice. The richer the catalog of usable mathematical patterns becomes, the less often users must restate mechanical intermediate steps, and the more clearly the source can preserve the mathematical spine. The same design direction appears in language conveniences such as `setting`. A `setting` is not a builtin rule, but it packages recurring parameters, conditions, and mathematical background into a reusable declaration, greatly simplifying what follows.

Hundreds of rules may sound complicated, but many of them work in a very direct way: check whether the current object or fact has a particular structural pattern, then reduce it to smaller premises. A pattern here can be compared to a “regular expression over mathematical objects,” but the implementation does not run a regular expression over source text. The parser has already converted the source into structured `Obj` and `Fact` values, and the Rust code matches the concrete shapes of those enums.

For example, when the goal is `x $in union(A, B)`, the mathematical pattern says that the goal follows if either `x $in A` or `x $in B` holds. The representative branch in the current Rust implementation says exactly that:

```rust
Obj::Union(set) => vec![
    vec![
        InFact::new(fact.element.clone(), set.left.as_ref().clone(), lf.clone()).into(),
    ],
    vec![
        InFact::new(fact.element.clone(), set.right.as_ref().clone(), lf.clone())
            .into(),
    ],
],
```

The outer `Obj::Union(set)` recognizes a binary union as the target set. The two inner `vec!` values represent alternative routes: prove membership in the left side, or prove membership in the right side. The checker continues through a bounded premise-verification entry point for these smaller facts and records the selected rule and child evidence on success. Many builtin rules can be understood in this way: they form an explicit catalog organized by mathematical shape, not an inexplicable black box.

More rules generally make Litex more comfortable to use, but they also enlarge the trusted implementation surface that must be audited. The Litex-to-Lean compiler is therefore more than an ecosystem integration feature; it is part of the correctness architecture that answers this tradeoff. For a supported route, the compiler must preserve the verifier-selected rule, premises, and fact citations, then replay that route through proved Lean theorems. An unsupported rule must stop compilation explicitly rather than being filled with a new axiom, `sorry`, or another proof hole. The existence of many rules cannot by itself prove that the entire kernel is correct, but this design allows each covered builtin route to receive an independent check from the Lean kernel.

<a id="appendix-examples"></a>
## Appendix B: Why Does Litex Have So Many Examples?

Litex's examples, dataset translations, and complete textbooks are first of all continuing stress tests of the language and kernel, not merely feature demonstrations. A carefully chosen small example may happen to avoid a system's weak points. Hundreds or thousands of examples spanning mathematical domains, proof shapes, and long-range dependencies continually force the syntax, runtime, well-definedness checking, builtin and inference rules, standard library, and diagnostics to work together. Complete textbooks matter especially because they test whether definitions, lemmas, and structures compose across chapters rather than only within an isolated theorem.

Many examples cannot by themselves prove soundness or establish that the architecture is the final correct design. They provide a different kind of important evidence: Litex is not working only on toy problems, and the same design can continue to express, check, and reuse facts across varied mathematical settings. Local bugs and design gaps become easier to discover in this process and can be reduced to permanent regression tests. Thus, “doing more exposes more problems” is not evidence against rigor; it shows that more real mathematics is entering the system's test surface.

The important question is therefore not only how many examples exist, but whether they preserve the original mathematics, compose in real contexts, remain continuously executable by the runner, and turn failures into reproducible boundaries. Within the compiler's supported scope, the same Litex example should also generate a Lean proof and pass the real Lean kernel. Examples then become more than claims about what Litex can do: they become executable evidence that can fail, be repaired, and increasingly be checked independently.

> **Litex builds many examples not to make problems harder to see, but to make it harder for the language to escape the test of real mathematics.**

<a id="appendix-conditions"></a>
## Appendix C: What Litex Is Doing About the Conditions for Success

The four layers of value in the conclusion do not follow automatically from Litex's interface. The current beta has invested in six concrete directions to test the conditions behind them; these are ongoing efforts, not a completed soundness, scalability, usability, or performance case.

1. **Make trust boundaries visible and independently checkable.** `trust`, `trust have`, and `axiom` are explicit source forms; ordinary file runs report unverified imports, while `-strict` verifies configured dependencies and rejects those trusted forms. Normal and detailed output separate why a fact was accepted, what was stored, what was inferred, and which direct trusted statements occurred. Verification routes increasingly carry structured evidence that the partial Litex-to-Lean compiler can replay through the Lean kernel, while unsupported routes fail closed instead of generating `sorry` or new axioms. The present boundary remains important: Litex records direct trusted statements but does not yet propagate a transitive trust label to every downstream fact, and Lean replay covers only a documented subset of the language and builtin rules. See the [system map](Litex_System_Map.md#reading-results-and-trust), [CLI trust controls](cli.md#global-options), and [compiler boundary](../lean/README.md).

2. **Pressure-test composition across long developments.** Litex's module system gives imports and exports a deterministic mathematical order and supports focused file checks as well as complete module runs. Registered multi-file textbook workspaces exercise definitions, theorems, namespaces, and dependencies across chapters instead of only inside isolated examples. These projects are continuing stress tests, not proof that arbitrary long developments already scale smoothly; see the [module contract](cli.md#project-modules) and [registered textbook workspaces](../scripts/.textbooks).

3. **Keep natural source from becoming invisible magic.** A concise fact can trigger local reconstruction, but the reading and audit views expose immediate `why_verified` reasons, well-definedness and verification phases, cited facts, builtin-rule premises, and failure boundaries; relation and fact graphs provide another view of those dependencies. Builtin rules are implemented as explicit mathematical patterns with named evidence, while focused positive regressions and nearby negative boundaries are the audit target rather than one undifferentiated automation command. This tooling makes the hidden work inspectable, but it does not by itself prove every rule correct or guarantee that every explanation is yet easy to understand; see the [CLI output contract](cli.md) and [Appendix A](#appendix-builtins).

4. **Reduce and measure total formalization cost.** The fact-oriented surface, bounded local proof search, compact feedback, registered-file execution, and persistent `-session -before` workflow are all attempts to reduce the effort and latency of writing and repairing proofs. Litex has not yet established a controlled, same-task, end-to-end cost advantage over mature alternatives; that claim requires measurements of author time, repair iterations, proof debt, runtime, and maintenance on representative mathematics, not a few short comparisons.

5. **Build a bridge to Lean instead of a knowledge island.** The repository contains a partial Litex-to-Lean compiler, a Lean semantic wrapper, paired generated examples, and real Lean kernel checks. The compiler retains verifier-owned fact identities, scopes, proof evidence, and well-definedness obligations for the routes it supports, while rejecting unsupported verified statements rather than silently inventing proof. Its coverage is still deliberately partial, so interoperability is a growing audit path and migration route rather than a general export guarantee; see [Litex: A Concise Mathematical Front-End Language for the Trusted Lean Ecosystem](#compatibility) and the [compiler's current support boundary](../lean/README.md).

6. **Use real corpora and preserve failure evidence.** Litex is being exercised on examples, multi-file textbooks, and dataset workspaces including MATH500, miniF2F, school mathematics, and longer undergraduate developments. Dataset runners, source-local todo files, proof journals, trust audits, and reduced regression cases are used to distinguish checked results from translated-but-incomplete work and to turn failures into language, library, inference, diagnostic, or kernel work. Corpus size alone is not evidence of capability: an item counts as checked evidence only when its registered gate passes, and mixed or unfinished corpora must remain labeled as such; see [Appendix B](#appendix-examples) and the [dataset runner sources](../src/main_test/lit_file_runner_tests/dataset_runners.rs).

Together, these efforts define an engineering and research program rather than a claim that the hard conditions have already been met. Litex earns the four values above only to the extent that trust stays auditable, long developments continue to compose, explanations remain inspectable, end-to-end costs fall on measured tasks, Lean replay expands without proof holes, and real failures remain visible.

Related links

1. To try Litex examples and inspect the generated output and knowledge graphs, visit [litexlang.com](https://litexlang.com).

2. For the Litex kernel implementation, see the [golitex repository](https://github.com/litexlang/golitex).

3. To read mathematics textbooks written in Litex, visit [Litex Mathematics Textbooks](https://litexlang.com/textbook).
