# Litex: A Formal Language Where Mathematics Verifies Itself

Created and maintained by Jiachen Shen.

Last updated: October 2, 2026.

Website: https://litexlang.com/doc/Litex_Blueprint

Chinese version: https://litexlang.com/doc/Litex中文蓝图

<!-- Blueprint spine: reasoning abundance from AI → scientific object → design hypothesis → measurable costs → potential capacity impact → dual bottlenecks of verification and understanding → two participation barriers → four language design choices → knowledge record left by each statement → Human–AI–Litex skill and knowledge-production protocol (including definition and verification) → replay, reuse, and Lean/Mathlib handoff of the record → ecosystem role → from AI for Math toward trustworthy, efficient reasoning in the AI era → success criterion -->

<!--
Litex four-layer positioning check (verify layer by layer while writing; emphasis may shift by audience, but layers must not be confused):
- Scientific object: how checkable knowledge is represented and constructed step by step.
- Scientific hypothesis: whether fact-oriented representation and transactional interaction form a new formal-language paradigm.
- Scientific result variables: how that paradigm changes the cost for humans and AI to construct, understand, audit, repair, and reuse knowledge, and how much candidate reasoning can be handled reliably per unit time.
- Societal impact: starting from AI for Math, lower the barrier to producing and auditing verifiable knowledge, so that verification capacity may keep pace with AI-generated candidate reasoning, and so that methods and infrastructure accumulate for broader trustworthy, efficient reasoning in the AI era.
Writing boundary: the first three layers are Litex's scientific core; the fourth is potential impact. Do not use “thereby” to present unverified scientific results as already realized tool effects.
-->

## Table of Contents

- [0. Litex Blueprint Overview](#overview)
  - [0.1 Five Main Threads: How Litex Works](#overview-spine)
- [1. Write Facts and See Why They Hold](#fact-oriented)
  - [1.1 Fact-Oriented: Writing “What Holds” into the Source](#fact-oriented-interface)
  - [1.2 What Each Statement Leaves Behind: Checkable Knowledge Records](#execution-model)
- [2. Start from Familiar Mathematics: Litex’s Set-Theoretic Foundation](#set-theory)
  - [2.1 The Design Difficulty: Making Concrete Mathematics a Working Language](#design-difficulty)
- [3. Let Established Knowledge Grow: Bottom-Up Proofs](#bottom-up)
- [4. Humans, AI, and Litex Advance Proofs Together](#interaction-loop)
- [5. Connect to Lean for Independent Rechecking and Mathlib Interoperability (Experimental)](#compatibility)
- [6. From Language to Ecosystem: The Role Litex Aims to Play](#ecosystem-role)
  - [6.1 Compiling Proofs to Executable Code (Python / C) (Experimental)](#executable-code)
- [7. The Art of Seeking What Is Different](#conclusions)
  - [Special Thanks](#special-thanks)
- [Appendix: Programming, Mathematics, and Formalization with Litex](#overview-readers)
  - [Personal Reflection: Does Litex Fill a Paradigm Gap in AI Reasoning?](#summary-bottom-up-and-top-down)
- [Appendix: Source Gallery](#overview-gallery)

<a id="overview"></a>

## 0. Litex Blueprint Overview

*Begun in 2024, Litex asks a question: can formal proofs stay close to ordinary mathematics, be easy to write and read, and still be rigorously checked? It hopes to become a Python for formal languages, bringing more people into the world of checkable mathematics. Put simply, Litex is not only a tool for formalization experts; it aims to lower the barrier and help more people gradually become experts themselves.*

To do this, Litex starts from the familiar set-theoretic world of sets, elements, functions, and relations. Authors choose definitions, constructions, and facts to prove; Litex checks for local grounds in the current knowledge and explains why a statement holds or where verification stops. Accepted facts stay in the context for later proofs. This explicit feedback also lets humans and AI try, revise, and accumulate checkable results together.

The next step on this path is Lean. The Litex-to-Lean compiler is not yet integrated into the current build and is expected to be completed by the end of 2026. Its goal is to let Lean independently recheck supported Litex proofs, connecting familiar mathematical expression to the existing formalization ecosystem.

These choices ultimately serve human understanding. Mathematics helps us understand the world we live in; Litex hopes to keep [fostering understanding](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/) in the AI era, when this ability may be easiest to lose and most important to retain.

<a id="overview-spine"></a>

### 0.1 Five Main Threads: How Litex Works

**These five threads show how Litex can build checkable mathematical knowledge step by step and put it to work for Math for AI.**

**1. I write what I want to prove, and the language explains why it holds.**

I still need to think through the proof and choose constructions and intermediate results. For local steps whose grounds can be found in the current knowledge, I want the language to carry out the checks and explain what it found.

For example, I can state an arithmetic fact directly:

```litex
1 + 1 = 2
```

The following statement record comes from the current CLI output. `proof_method` explains the grounds, while `stores` records facts that can be used later:

```json
{
  "success": true,
  "statement": "1 + 1 = 2",
  "proof_method": {
    "type": "builtin_rule",
    "rule_name": "Calculation",
    "message": "Both sides evaluate to the same number"
  },
  "stores": ["1 + 1 = 2"],
  "infers": []
}
```

I can also define oddness and then state a concrete judgment:

```litex
prop is_odd(x Z):
    x % 2 = 1

$is_odd(3)
```

The JSON record for `$is_odd(3)` shows that the language checks the fact by unfolding the definition and retains the resulting concrete facts:

```json
{
  "success": true,
  "statement": "$is_odd(3)",
  "proof_method": {
    "type": "by_definition",
    "rule_name": "By definition",
    "message": "Verified by unfolding a definition"
  },
  "stores": ["$is_odd(3)"],
  "infers": ["3 $in Z", "3 % 2 = 1"]
}
```

These records let both people and AI see whether a statement passed, what kind of grounds the language found, and what the step left behind.

**2. I can start from a mathematical world I already know.**

Litex is based on ZFC and organizes mathematics through sets, elements, functions, and relations. I want readers learning formalization to keep using their mathematical intuition and familiar ways of expressing ideas as far as possible.

For example, real numbers, sets, functions, and relations can appear together in one small example:

```litex
have a R = 2

have S set = {x R: x > 0}

have fn f(x R) R = x^2

prop is_less(x, y R):
    x < y

$is_less(2, 4)
```

`have a R = 2` introduces both `a $in R` and `a = 2`. `S` is the set of positive real numbers, `f` is the square function on the reals, and `is_less` expresses strict inequality between two reals. The final statement verifies the concrete relation `2 < 4`. These objects follow the organization of everyday mathematics.

**3. The language can retain the knowledge we have established and use it again.**

Every step forward in a proof should leave something that later steps can depend on. Objects, definitions, and verified facts together form the current mathematical context, on which new reasoning can continue to grow.

For example, we can prove Cantor's theorem ourselves: every function \(f:X\to\mathcal P(X)\) misses some subset and therefore cannot be surjective. The code below first defines what it means for a subset to have no preimage, proves the general result using a diagonal set, and then applies it to a concrete function. The whole example uses no `trust`:

```litex
prop has_no_preimage(X set, f fn(x X) power_set(X), D power_set(X)):
    forall a X:
        D != f(a)

thm cantor:
    ? forall X set, f fn(x X) power_set(X):
        exist D power_set(X) st {$has_no_preimage(X, f, D)}

    have D power_set(X) = {x X: not x $in f(x)}

    thm diagonal_nonmembership:
        ? forall a X:
            D = f(a)
            =>:
                not a $in f(a)
        by contra:
            ? not a $in f(a)
            a $in {x X: not x $in f(x)}
            impossible a $in f(a)

    claim:
        ? forall a X:
            D != f(a)
        by contra:
            ? D != f(a)
            not a $in f(a)
            a $in D
            a $in f(a)
            impossible a $in f(a)

    by def $has_no_preimage(X, f, D)
    witness exist E power_set(X) st {$has_no_preimage(X, f, E)} from D

have fn singleton(n N) power_set(N) = {n}
obtain missing from exist S power_set(N) st {$has_no_preimage(N, singleton, S)}
missing != singleton(0)
```

This example shows how knowledge accumulates during a proof and remains available for further use. Once we have defined the concept and proved Cantor's theorem, those results become part of the current mathematical context. When we introduce the concrete function `singleton`, Litex can use the general conclusion already proved to obtain new objects and facts for subsequent reasoning.

**4. AI can work with people to advance proofs through explicit feedback.**

AI can help try different approaches, fill in steps, and correct errors. People focus on the problem and its mathematical meaning; Litex provides verification feedback. Their shared work should accumulate checkable results.

```mermaid
flowchart LR
    Human["Human: problems and mathematical judgment"] --> AI["AI: propose and revise proofs"]
    AI --> Litex["Litex: verification and feedback"]
    Litex --> AI
    Litex --> Knowledge["Verified knowledge"]
    Knowledge --> Human
    Knowledge --> AI
```

**5. A written proof should ultimately be checked again by Lean.**

I want expressions closer to everyday mathematics to compile into Lean proof objects, receive an independent check, and connect to the existing ecosystem. The current build has not yet integrated this compiler entrypoint; it remains a goal for Litex to implement.

For example, consider a Litex arithmetic fact:

```litex
1 + 1 = 2
```

Using the representation from the repository's earlier compilation experiment, the corresponding Lean proof can be written as:

```lean
import Litex

theorem one_add_one : Litex.Same ((1 : ℂ) + (1 : ℂ)) (2 : ℂ) := by
  exact Litex.Same.ofEq (by norm_num)
```

`Litex.Same` is the equality relation in that compilation layer. The minimal Lean fragment above has been checked by Lean. It illustrates the target proof form; the current Litex build still has no compiler entrypoint that generates it.

Whether you are a mathematician, a programmer, or a Lean user, Litex can offer new knowledge and perspectives; if you are interested, continue with [Programming, Mathematics, and Formalization with Litex](#overview-readers) at the end of this document.

The following chapters develop these five threads in order, then discuss the language ecosystem; reader comparisons and further source examples appear in the appendices.

<a id="fact-oriented"></a>

## 1. Write Facts and See Why They Hold

<a id="fact-oriented-interface"></a>

### 1.1 Fact-Oriented: Writing “What Holds” into the Source

**Fact-centered**: the source records “what holds”; the verifier matches builtin rules, known facts, and definitions by shape, performs constrained matching and replacement, and checks well-definedness.

Every mathematical proof consists of “what to prove” and “how to prove it.” When reading mathematics, our usual mental flow is: see a sentence in a book, react in the mind to why that sentence is true, and once it is confirmed, remember it for later reasoning.

What Litex does is essentially to implement that mental flow on a machine. *Users write “what to prove”; the kernel matches by shape and checks why the statement holds.* At the same time, Litex stores already proved facts. When the user enters the next mathematical statement, Litex searches the context for grounds, checks well-definedness, and returns a verification result or a stopping point.

> **The core human–machine division of labor in fact orientation is: the user writes “what I want to prove,” and Litex searches for “how this fact can be verified.”**

This is not only an interface preference; it also saves a real cost: users need not first remember which tactic or lemma to name for every common equality—for example, numeric calculation need not hand-write `norm_num`, and polynomials need not hand-write `ring`. Key choices, witnesses, and estimates are still written by the author; concrete rules and equality alignment are searched for and recorded by the kernel. Litex triggers local search from facts; every result must be checkable: Litex looks for builtin rules, universal facts, concrete facts, or equalities by relation, argument shape, and context. Search is limited to supported scope; it is not free guessing.

#### How Litex Helps Users Search Verification Routes by Fact Shape

When verifying a fact, Litex is not “inventing a proof.” A closer picture is constrained lookup: split the current goal into a predicate and an argument shape, then search the context and rule tables—somewhat like Ctrl+F by shape. The predicate name of an atomic fact (such as `>=`, `$is_positive`, or `$in`) is the key into those tables; after a hit, the kernel instantiates or replaces and checks that premises are ready; if nothing matches, it stops at the current goal. **The essence is matching and replacement under supported rules, not unrestricted proof search.** This indexing can keep local checks light; actual time and memory use still need measurement on matched tasks and comparable libraries. The architecture alone does not establish that Litex is usually faster than Lean.

Common matching targets fall into four kinds:

| What is matched | What the kernel does | Minimal example |
| --- | --- | --- |
| **Builtin rules** | Filter rules by predicate/argument shape, then check premises | Given `x >= 0`, `y >= 0`, match “sum of nonnegatives is nonnegative,” get `x + y >= 0` |
| **Known concrete facts** | Find a same-shaped fact in context; align spelling by equality if needed | Given `$is_positive(a)` and `a = b`, match and rewrite to `$is_positive(b)` |
| **Known `forall`** | Match the goal shape to a universal fact, instantiate, check premises | Given `forall x R: x > 1 => $is_positive(x)` and `b > 1`, get `$is_positive(b)` |
| **Definitions** (`def` / `prop`) | Match a named predicate with its definition body by shape | Given `a > 0`, match `prop is_positive`, get `$is_positive(a)` |

```litex
prop is_positive(a R):
    a > 0

# 1) Match a builtin rule
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y

# 2) Match a known fact, then rewrite by equality
forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)

# 3) Match a known forall (store the universal; then from b > 1 get $is_positive(b))
forall x R:
    x > 1
    =>:
        x > 0
        $is_positive(x)

have b R:
    b > 1

$is_positive(b)

# 4) Match the definition of prop is_positive
have a R:
    a > 0

$is_positive(a)
```

Ordinary builtin-rule entry is controlled by `can_use_builtin_rule: bool`.
Builtin premises disable that entry and use known evidence or computation;
one checked function-body substitution may finish without another definition
unfold. Deep search, including definitions and known forall, uses a budget of 3;
strategy recursion has a separate budget of 16.


Users remember these shape patterns; the kernel maintains fact and rule tables and does the naming and alignment for you.

<details>
<summary><strong>Why can Litex maintain a fact table? Could Lean be extended to do the same?</strong></summary>

A natural question is: if Litex can maintain a fact table in the kernel so that users need not write `by xxx`-style tactics by hand, could Lean be extended to offer the same default mechanism? The answer is that it is **very difficult**—not mainly as an engineering backlog, but because of what the language may quantify over.

By design, Litex does not allow forms such as `forall p prop` that quantify over propositions themselves. Every atomic fact has a nameable predicate head; the kernel uses that predicate name as a key to retrieve candidate facts and rules, then matches and replaces by shape. Because the key is fixed, search stays an indexed local lookup rather than blind trial over the whole context—and users need not name common grounds by hand.

Once a language allows `prop`—or even facts themselves—to appear as parameters of `forall`, an atomic goal no longer guarantees a stable predicate name as an index. Without a fixed key, the candidate set expands toward nearly the entire context, or even the space of all expressible propositions. Maintaining a shape-indexed fact table and sparing users from tactic naming then become hard to hold together: one either falls back to explicit naming, or faces uncontrolled global search.

This does not deny the usefulness of Lean automation such as `simp` or `grind`. It says that a **default fact table indexed by predicate names depends on the language boundary that propositions are not arbitrarily first-class under quantification**. Dependent type theory opens that boundary by making propositions and proofs highly first-class. Litex trades that expressive freedom for an indexable fact context.

</details>

The following three Lean–Litex comparisons show several of these kinds of matching through complete interface examples. Lean source of course also contains a theorem statement that states the goal, and Litex also allows explicit theorems and proof structure; the difference is the default center of attention:

| Typical interface | What the source mainly presents | What interactive output mainly presents |
| --- | --- | --- |
| Lean tactic proof | The theorem statement gives the goal; the tactic proof body mainly writes **how**: how to rewrite, apply a theorem, or close the goal | Infoview shows **what**: what still needs to be proved |
| Litex fact-oriented proof | The source mainly writes **what**: which objects, conditions, and facts should hold | Verification output explains **how**: why a fact was accepted, or where verification stopped |

> **A mirror relation of default interfaces: Lean tactic source mainly writes how, while Infoview shows unfinished what; Litex source mainly writes what, while Litex output explains the how found by the verifier.** This compares typical workflows; it is not an absolute summary of every writing style in either language.

The Litex JSON below is an excerpt of explanatory output. It shows how the current version records verification routes; field names, nesting, and message text may change across Litex versions.

<details>
<summary><strong>Example 1: how Lean and Litex verify “the sum of two nonnegative reals is still nonnegative”</strong></summary>

**Builtin rules.** Litex splits the goal into a predicate and an argument shape, filters candidate rules accordingly, then checks that types, premises, and conditions all hold.

The mathematical fact to prove is: the sum of two nonnegative reals is still nonnegative.

**Lean source｜proof body writes how**

```lean
import Mathlib

example (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : x + y ≥ 0 := by
  exact add_nonneg hx hy
```

Before that last line runs, Infoview shows the unfinished **what**:

**Lean Infoview｜shows what**

```text
x y : ℝ
hx : x ≥ 0
hy : y ≥ 0
⊢ x + y ≥ 0
```

**Litex source｜writes what directly**

```litex
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y
```

This source does not name a rule. The goal `0 <= x + y` can be expressed as the predicate `>=` and the arguments `x + y`, `0`; the kernel filters candidates accordingly, matches the two nonnegative premises, and continues to check types and conditions.

**Litex output｜explains how**

```json
{
  "kind": "run",
  "success": true,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "forall x, y R: /     0 <= x /     0 <= y /     =>: /         0 <= x + y",
      "proof_method": { "type": "..." },
      "stores": ["..."],
      "infers": []
    }
  ]
}
```

</details>

<details>
<summary><strong>Example 2: how Lean and Litex reuse a universal fact</strong></summary>

**User-supplied universal facts.** A proved `forall` fact enters the context; when a same-shaped goal appears, Litex matches parameters and checks the instantiated premises.

The second mathematical fact is: if a real `a > 10`, then there exists a positive real strictly less than `a`. The earlier universal fact can then be used directly for a concrete `a`.

**Lean source｜proof body writes how**

```lean
import Mathlib

def HasPositiveWitness (n : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ n > a

theorem hasPositiveWitness_of_gt_ten (x : ℝ) (hx : x > 10) :
    HasPositiveWitness x := by
  refine ⟨10, by norm_num, ?_⟩
  exact hx

example (a : ℝ) (ha : a > 10) : HasPositiveWitness a := by
  exact hasPositiveWitness_of_gt_ten a ha
```

Before the last line runs, Infoview gives the current **what**; the `exact` in the source specifies the **how** that completes it:

**Lean Infoview｜shows what**

```text
a : ℝ
ha : a > 10
⊢ HasPositiveWitness a
```

**Litex source｜writes what directly**

```litex
prop is_positive(n R):
    exist a R+ st {n > a}

claim:
    ? forall x R:
        x > 10
        =>:
            $is_positive(x)
    witness exist a R+ st {x > a} from 10

have a R:
    a > 10

$is_positive(a)
```

Here `prop` gives a reusable interface; `claim` establishes an instantiable universal fact. The later `have` supplies a concrete premise, and the final source writes only `$is_positive(a)`, without again writing how to call the universal fact.

**Litex output｜explains how**

```json
{
  "kind": "run",
  "success": true,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "$is_positive(a)",
      "proof_method": { "type": "..." },
      "stores": ["..."],
      "infers": []
    }
  ]
}
```

</details>

<details>
<summary><strong>Example 3: how Lean and Litex transport a concrete fact along an equality</strong></summary>

**Concrete facts and known equalities.** Litex can also start from a concrete fact in the context and use a known equality to align arguments that are written differently but equal.

The third mathematical fact is: given that `a` is positive and `a = b`, conclude that `b` is positive. Here one needs equality to transport a concrete fact to another writing.

**Lean source｜proof body writes how**

```lean
import Mathlib

def IsPositive (x : ℝ) : Prop :=
  x > 0

example (a b : ℝ) (ha : IsPositive a) (hab : a = b) : IsPositive b := by
  simpa [hab] using ha
```

Before `simpa [hab] using ha` runs, Infoview only presents the current **what**:

**Lean Infoview｜shows what**

```text
a b : ℝ
ha : IsPositive a
hab : a = b
⊢ IsPositive b
```

**Litex source｜writes what directly**

```litex
prop is_positive(x R):
    x > 0

forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)
```

The Litex source preserves premises and conclusion; it does not write `simpa` or specify a rewrite direction. The verifier finds `$is_positive(a)` from the context and then uses `a = b` to align arguments.

**Litex output｜explains how**

```json
{
  "kind": "run",
  "success": true,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "forall a, b R: /     $is_positive(a) /     a = b /     =>: /         $is_positiv",
      "proof_method": { "type": "..." },
      "stores": ["..."],
      "infers": []
    }
  ]
}
```

</details>

<details>
<summary><strong>Personal observation: an analogy with imperative and declarative programming</strong></summary>

The same twist is discussed in more detail in [“For programmers” at the end of this document](#reader-programmers): functional style leans toward *what*, imperative style toward *how*; Lean is a functional language, yet tactic proofs often read as imperative *how*, while Litex’s default mathematical surface returns to *what*. The point here is only the analogy: each Lean tactic line changes the current Goal much as an imperative statement changes program state; Litex asks the author to write the fact that should hold and lets the verifier search for *how*.

</details>

<details>
<summary><strong>Place in the design space: searching for local proof grounds is not unique to Litex</strong></summary>

[Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/),
[Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html),
and [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) provide local automation through explicit proof tactics or
proof methods; [Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf)
has empty justification;
[ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM) can attempt to prove a theorem event without hints;
[Naproche](https://naproche.github.io/) uses automated theorem provers
to check steps in controlled natural language. Litex more specifically tests whether ordinary mathematical statements can trigger local verification limited by the current context and rules, then write back to the context when they succeed and display verification sources.

Local automation can sit on many kernels. Litex emphasizes another route: trading away arbitrary quantification over `prop` / facts for a fact table indexed by predicate names, so the default proof need not rely on explicit tactic naming. This is the same design boundary as in “Why can Litex maintain a fact table?” above.

</details>

<a id="execution-model"></a>

### 1.2 What Each Statement Leaves Behind: Checkable Knowledge Records

**Traceable proof flow**: the system organizes and outputs the mathematical grounds for each statement, together with the forward and backward dependencies from definitions and premises to conclusions, so that the proof process becomes structured information that is readable, checkable, and reusable—beyond reading the source, you can also read the principles behind it; on failure, it points to where the failure occurred.

When we read mathematics, a sentence never appears in isolation. As we write down a fact, we also recall in the mind the definitions, premises, and previously confirmed facts it depends on; together they form a growing context, and later reasoning continues on that already established foundation.

What Litex aims to do is turn that mathematical mental flow—usually present only in the mind—into code sentence by sentence: the source writes the objects to introduce and the facts to verify; already defined concepts and already proved facts remain in the context; later statements continue to grow on top of them.

*What makes Litex most distinctive is that its running process is not a black box. How any statement holds, what concepts it introduces, and what effect it has on the whole proof context are all output.* In other words: you are not only reading the source itself; beyond the source, the mathematical grounds behind each statement are laid out for you—the language helps you prove; you say what to prove. Precisely because Litex has such structured output, it can be compiled to Lean (or any formal language) relatively easily, and the relations among concepts and among facts throughout a mathematical proof can be presented strictly. It records and outputs why each sentence holds, which grounds were used, what inferences were produced, and which content truly entered the later mathematical context.

First consider a minimal contiguous fragment:

```litex
let a = 1
a + 1 = 2
```

The first sentence is a definition (`define`): it introduces an object and stores the defining fact `a = 1` in the context. The second sentence is verification (`verify`): it reads the current context, checks well-definedness of `a + 1 = 2`, performs transparent definition reduction along `a = 1`, then uses a numerical normalization rule. After it succeeds, the second fact enters the current context and becomes a basis later statements can continue to use.

Below is the execution result of this fragment.

<details>
<summary><strong>Expand: Litex execution result</strong></summary>

```json
{
  "kind": "run",
  "success": true,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "let a = 1",
      "proof_method": { "type": "define_obj" },
      "stores": ["a = 1"],
      "infers": []
    },
    {
      "success": true,
      "statement": "a + 1 = 2",
      "proof_method": {
        "type": "builtin_rule",
        "rule_name": "Calculation",
        "message": "Both sides evaluate to the same number"
      },
      "stores": ["a + 1 = 2"],
      "infers": []
    }
  ]
}
```

</details>

This record splits “why this sentence can be written down” into traceable local steps: first confirm that the arguments of `a + 1` satisfy the set conditions required by the operation; then transparently reduce along the defined `a = 1` to `1 + 1 = 2`; finally complete the calculation by a numerical normalization rule. For a reader, it answers at least five local questions:

| What the reader wants to know | What to look at in the record |
| --- | --- |
| Which statement ran | `statement` |
| Whether it succeeded | statement `success`, and run `success` / `session_error` |
| Why it holds | `proof_method` (rule name, cite, definition route, …) |
| Why it stopped | `why_failed.phase` and `why_failed.goal` |
| What entered the later context | `stores` and `infers` |

Normal JSON is the user-facing record. The full verify/exec evidence tree remains available for Lean replay and detailed tooling; it is not what everyday `-e` / `-f` / `-r` prints.

For example, `let a = 1` defines the symbol `a` and records `a = 1`; `a + 1 = 2` verifies a fact in the current context. Well-definedness first confirms whether the statement is meaningful: for instance `1 / 0 = 1 / 0` has the same form on both sides, but `0` is not an allowed denominator for division, so the statement fails the well-definedness requirement.

<details>
<summary><strong>Expand: Litex execution result</strong></summary>

When we enter `1 = 0`, Litex's Normal JSON output is

```json
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": false,
      "statement": "1 = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "1 = 0"
      },
      "stores": [],
      "infers": []
    }
  ]
}
```

Such error output is also valuable. When we design the human–AI–Litex interaction flow, we can record mistakes we once made, accumulate more experience of mathematical formalization, and make writing code more efficient and correct over time.

</details>

*The core of Litex is this concise, rigorous, formatted verification-flow output—it turns “why this sentence holds” from tacit mental knowledge into a readable record.* Starting from an execution path that a user can read and take part in, Litex also retains a structured knowledge record. That record serves four roles:

1. **For human reading**: turn statements, grounds, and context changes into an interactive textbook. You read the source; you simultaneously receive the mathematical principles behind it. Beginners need no longer stop because they do not know why a sentence holds.
2. **For AI collaboration**: return grounds of each success, stop, and failure to AI, so that it can write Litex, auto-correct from feedback, and improve step by step, forming a human–AI–Litex loop.
3. **For knowledge structure**: generate dependency graphs of definitions and theorems from definitions, facts, citations, and inferences, visually showing how concepts connect.
4. **For Lean rechecking**: design a Litex-to-Lean compiler from the definitions, facts, and verification grounds in the record, hand generated equivalent Lean code to the Lean kernel for rechecking, and connect to the Lean ecosystem.

![Litex fact-relation graph example](https://litexlang.com/_next/image?url=%2Fassets%2Fknowledge_graph.png&w=640&q=75)


I believe the functions of this output stream go beyond those listed above. We hope more scenarios will be discovered in the future AI era.

<details>
<summary><strong>Summary: which mathematical views Litex's design embodies</strong></summary>

Litex treats mathematical practice as a back-and-forth of two actions:

1. **Define** (`define`) builds objects, relations, functions, and reusable interfaces, giving a domain its vocabulary.
2. **Verify** (`verify`) confirms which facts hold in the current context and stores their grounds.
3. Every accepted statement changes the premises available to later proofs; earlier text is not background decoration but the foundation of what follows.
4. Verification results retain both “why it holds” and inferences within their applicable scope, rather than only a true/false label.
5. Common mathematical correspondences are preferably supplied by a small set of composable objects, relations, logical structure, builtin rules, and a standard library; the goal is to cover broad set-theoretic mathematics, not to add an overlapping special interface for every phrasing. Current coverage continues to expand and be audited.

Any one of these five points, taken alone, is not unique to Litex; other languages may also do well in one direction. Litex's design emphasis is to combine them into one continuous mathematical workflow: definition builds vocabulary, verification confirms facts in the current context, the record stores grounds and inferences, later statements continue to grow on earlier ones, and the same record simultaneously serves humans, AI, dependency graphs, and Lean. It is this combination that brings formalization closer to everyday mathematical thinking, makes it more suitable for AI participation, better fits the mathematical pursuits of the AI era, and takes human understanding and judgment as the starting point. This is the design hypothesis Litex is testing, not an exclusive claim about other languages' capabilities.

Most importantly of all: Litex is a tool that can truly help people understand mathematics. It does not only tell you the answer; it lays out why the answer holds, what it depends on, and what it leaves for later text. In the AI era, when answers can be generated in bulk, this ability to help people keep understanding is especially precious.

</details>

<details>
<summary><strong>Implementation summary: how the record is generated</strong></summary>

The implementation can expand with rules, the standard library, knowledge graphs, and Lean interfaces without changing the reader's understanding of the core process:

```text
Litex source
  → parse into typed objects and statements
  → execute definition or verification
  → check well-definedness, shape, grounds, and premises
  → produce a structured execution result
  → commit the candidate or roll it back
  → update the accepted context, and run inference when applicable
  → let humans and AI see accepted paths, context changes, and repair boundaries
  → retain a checkable knowledge record for tools and interactive views
  → provide machine-readable or structured views such as JSON and relation graphs when needed
  → future integration: hand supported evidence to a Lean compiler and kernel
```

A checkable knowledge record is the structured form of this visible execution path, not a log pieced together after the fact from terminal text. JSON is one machine-readable representation used when tools need it; users need not read JSON to follow and repair the execution. Relation graphs are an optional view of connections; Lean is an independent rechecking endpoint for supported routes. Implementation scale can grow, but these responsibilities need not inflate with the number of rules.

</details>

<a id="set-theory"></a>

## 2. Start from Familiar Mathematics: Litex’s Set-Theoretic Foundation

**Set-theoretic objects**: users directly see sets, elements, functions, and relations, without first managing abstract carrier types.

The axiomatic system chosen by a formal language directly determines the boundary of its expressive power and the style of its source. Litex chooses the most widely familiar set theory as its foundation, avoiding the extra learning cost of dependent type theory or other axiomatic systems. Its objects are sets, elements, functions, and relations; its facts are membership, subsets, intersections and unions, function application, and equality.

For example, if `s` is contained in `t`, then after intersecting each with the same set `u`, the former is still contained in the latter:

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

As one can see, this writing is very close to the set-theoretic statements we meet in everyday mathematics.

Below is the Lean version of the same mathematical statement from the set-theory chapter of *Mathematics in Lean*:

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

Lean first declares a common element type `α : Type*`, then declares `s`, `t`, `u : Set α`. This makes the theorem reusable over any element type; `Type*` also involves the universe hierarchy of types.

The difference is not that “shorter code is stronger”: Lean can also finish this with a short proof or automation; here the textbook's expanded path is kept on purpose. The real distinction is the default interface: Lean first gives sets a type-theoretic carrier and then constructs a proof; Litex directly recognizes and checks common set-theoretic facts.

> **Set theory decides how objects are shaped; it does not decide which layer you start from each day.**

Choosing set theory as the foundation is often heard as two claims—really two misreadings.

<details>
<summary><strong>Two misreadings: neither “learn set-theoretic encoding first” nor “rebuild everything from ZFC”</strong></summary>

**Misreading 1: If I am not fluent in set theory, I cannot express ordinary notions such as groups, topological spaces, or open sets with ∈ and ∪.**  
This is first a **dictionary problem**, not a prerequisite course in set theory. How everyday mathematics says it should have a readable Litex counterpart. Groups and topological spaces (with their open-set families) can be written as working-layer interfaces, without first hand-coding a low-level encoding:

```litex
# Group: carrier set, operation, identity, inverse, and the usual laws
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

# Topology: a space is its carrier together with a family of open sets
prop is_topological_space(X set, open_sets power_set(power_set(X))):
    {} $in open_sets
    X $in open_sets
    forall U, V open_sets:
        intersect(U, V) $in open_sets
    forall family power_set(power_set(X)):
        family $subset open_sets
        =>:
            family_union(family) $in open_sets
```

An open set is simply a member of that family: under the explicit assumption `$is_topological_space(X, open_sets)`, writing `U open_sets` means that `U` is open. The group–Lean comparison below is a fuller interface contrast; here the point is only what the “dictionary” looks like. Coverage is still expanding; this is not a claim that every common notion is already catalogued.

**Misreading 2: If the foundation is set theory, must every development rebuild analysis, algebra, and topology from the ZFC axioms—and would that not be too hard?**  
This is an **entry-height problem**. Litex does expose set-theoretic / ZFC-side axiom and constructor interfaces for foundational work or when one needs to dig downward. Ordinary use does not force unfolding the concrete set-theoretic constructions of common concepts: for objects and structures familiar in everyday mathematical writing, the system supplies checkable relations and usage surfaces so you can operate at the abstraction layer you want, rather than first building up to that layer from the axioms. The low-level interfaces are an exit and escape hatch, not the staircase you must climb every day.

More precisely: Litex's builtin layer cares about **checkable relationships** among objects, statements, and facts—not about picking one “true” concrete construction as the definition. Rational numbers `Q` and real numbers `R` admit many set-theoretic constructions; a function may be modeled by different graph encodings. The builtin interface does not make any one of these the unique definition; it exposes usable relations such as membership, inclusion, and the domain–codomain behavior of function application. When a particular construction matters, a development may write it explicitly, or mark an assumed compatibility result with `trust`.

So: set theory fixes the shape of the object language; **the working entry point** remains yours—you may start from a working layer such as groups or topology, and drop to axiom interfaces when needed. The sketches above and the group comparison below demonstrate working-layer writing; they do not ask the reader to finish a construction that begins from the empty-set axiom.

</details>

<details>
<summary><strong>Technical summary: typing judgments and membership facts</strong></summary>

Lean organizes mathematics as typed terms: after elaboration, core expressions are checked by judgments of the form `Γ ⊢ e : T`. The colon belongs to a meta-level typing judgment; it is not an ordinary proposition in Lean's object language that can be accumulated alongside equality, order, or theorem facts. Surface overloading and coercions can elaborate similar writing into different core terms, but each resulting term is checked under a definite type.

Litex organizes mathematics as objects and a gradually growing fact context. `e $in S` is a membership fact in the object language, at the same logical layer as equality, order, and other predicates. Therefore the same object can be proved to belong to several unrelated or overlapping sets: membership is a relation among objects, not a unique intrinsic assignment `typeOf(e) = S`.

Object capability lookup uses the facts stored for the object's canonical
identity. The execution environment's `special_properties` index retains actual
membership and equality facts, including facts learned after a name's
introduction. Function-call checking reads signatures from these facts;
function-body unfolding follows and cites stored equalities. For example,
`have fn f(x R) R = x + 1` followed by `let g = f` supports `g(4) = 5` directly.
Membership `g $in fn(x R) R` alone supplies callability without a concrete value.
Definition-selected default struct field views remain a distinct annotation.

This does not cancel static constraints or inference. Before accepting an expression, Litex still checks domains, return sets, structure fields, and other well-definedness obligations, and derives membership and carrier facts in proofs through dedicated rules. The difference is that such inference adds facts such as `e $in S` to the context, rather than inferring a privileged type `e : T` that decides the object's identity.

Lean's core is based on dependent type theory; Litex chooses to organize user-facing mathematics through sets and membership facts. Lean's `Set α` can also express set-theoretic mathematics, and Mathlib offers rich mathematical interfaces. The difference is in how each language asks authors to introduce objects, state facts, and supply verification grounds by default. Litex's current coverage is still expanding; a shared mathematical goal does not mean the two systems already have identical scope. Litex's verifier and builtin rules form their own trusted implementation surface, which makes independent Lean rechecking an important goal. The earlier compiler experiment is not wired into the current build.

</details>

<a id="design-difficulty"></a>

### 2.1 The Design Difficulty: Making Concrete Mathematics a Working Language

“More concrete” describes the default mathematical vocabulary presented to authors. It does not mean that Lean can only be written at a low level. As the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/) explains, Lean's surface syntax is elaborated into expressions in its core type theory, whose proof terms the kernel checks; compiler IR for executable programs belongs to a separate path. Lean also provides notation, automation, and Mathlib. Litex instead lets authors work directly with sets, elements, functions, and facts: `have a R = 2` introduces an object and leaves both `a $in R` and `a = 2`. The important difference is the default working interface, rather than exclusive access to ordinary mathematics.

The difficulty is not adding familiar LaTeX symbols to a grammar. For a language to carry substantial proofs, arithmetic, set construction, functions, relations, quantifiers, witnesses, contradiction, and induction must work in combination. In the Cantor example above, `{x X: not x $in f(x)}` combines bounded set construction, function application, negation, and membership. Such combinations need explicit well-definedness conditions, checkable grounds for acceptance, reusable facts after success, and feedback that locates failure. Adding a notation completes only one part of that work.

Litex leaves key constructions, intermediate claims, and witnesses to the author, while the verifier looks for local grounds; `claim`, `witness`, `by contra`, and induction remain available when explicit proof structure is needed. This division moves some complexity from authors into the language implementation. Its rules must cover enough common cases while remaining consistent and auditable when features interact. Litex is working toward rigorous checking, broad practical coverage, and ease of use together. Support for familiar LaTeX notation does not mean every proof is already supported. Current coverage and the planned independent Lean check still need to be assessed through examples, recorded failures, and further implementation.

<a id="group-comparison"></a>

<details>
<summary><strong>Small example: defining the same mathematical object under different axiomatic systems</strong></summary>

When the standard library does not cover a domain, can users build a theory from a small set of shared concepts? Sets, functions, relations, and operations are a shared language across domains, letting definitions and theorems grow along their own mathematical dependencies rather than first obeying an external library's encoding. This is **bootstrapping a mathematical theory**.

Mature libraries certainly speed construction, but they should not be a precondition for expressing a new domain. The two group fragments below express the same structure and uniqueness of the identity, yet present different interfaces for carriers, operations, and laws.

A group consists of elements, a binary operation, an identity, and inverses, satisfying associativity, identity laws, and inverse laws. If another element also behaves as an identity for every element, it must coincide with the original identity.

#### Lean: a record type over `Type` and curried functions

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

Lean specifies the element type with `Carrier : Type`, and later operations and laws depend on it. `Carrier → Carrier → Carrier` is a curried binary function that takes two elements in turn; associativity and identity laws become named fields such as `mul_assoc` and `one_mul`. This helps abstraction and large-library reuse; authors must also know which field to call in a proof and in which direction an equality is used. The example above explicitly calls `G.one_mul`.

#### Litex: operations on a set and structural facts written directly

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

Litex first binds a nonempty set `s`, then writes the group as a structure on it. `mul fn(x, y s) s` means the operation takes two elements of `s` and returns a result still in `s`; the group laws are written as ordinary facts under `<=>:`. Uniqueness of the identity is then written directly as an equality chain, and the kernel searches for identity-law grounds. Long-lived results can still be named as a `thm`, but local facts need not all become interfaces that must be memorized first.

Field paths such as `G.mul` are checked against the declared structure carrier; the path itself does not add the group axioms to the context. Directly binding `G &Group<s>` opens one layer automatically. A struct definition also publishes universal laws over its parameters and instance; inner consequent universals are flattened without changing premises or existential dependencies. Ordinary known-forall matching can use those laws when the exact carrier and conditions verify. `release struct def expression` still verifies membership before materializing one layer of representation and property facts; a later membership fact alone does not eagerly unpack the value.

Of course Lean can also define a group without Mathlib; what is compared here is the default experience, not the expressive upper bound. “Building from scratch” is not dependency-free either: Litex still depends on its kernel, rules, and standard library, and external libraries remain important accelerators—they simply should not become an expressive boundary. The “two misreadings” above already say that working-layer writing is not rebuilding from ZFC; the group fragment here demonstrates entry height, not a foundations homework set.

The group is only a small demonstration. A stronger test is whether a small team can build readable, extensible interfaces with clear boundaries for domains that existing libraries cover poorly. Future libraries in geometry and other areas should show progress through dated source, verification results, `trust` boundaries, and real reuse notes, rather than claiming success in advance.

</details>

<details>
<summary><strong>Place in the design space: set-theoretic presentation is not Litex's invention</strong></summary>

[Mizar's mathematical library](https://wiki.mizar.org/library/) is based on Tarski–Grothendieck set theory;
[Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) and
[Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) present dependent type theory kernels to users;
[Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
uses polymorphic higher-order logic.

Litex's user-facing propositional language is broadly first-order in style: atomic relations or named predicates are organized through restricted classical logical forms and quantifiers. It prefers canonical fact shapes; propositions and proofs cannot be arbitrarily combined as ordinary first-class values—so forms such as `forall p prop` are disallowed; Section 1 explains how that keeps the fact table indexable by predicate name. This describes only the propositional interface; the verifier also checks well-definedness and searches for grounds from definitions, context, and supported rules.

In this background, Litex's question falls more specifically on the user-facing object interface:
can a small, membership-centered set-theoretic surface cover substantial mathematics without requiring users to manage type
universes first?

</details>

<a id="bottom-up"></a>

## 3. Let Established Knowledge Grow: Bottom-Up Proofs

**Bottom-up accumulation**: every verified fact enters the context for later reasoning; this is the default direction of reasoning.

There are two modes of mathematical thinking: one starts from premises, accumulates more and more intermediate conclusions, and finally reaches the desired conclusion; the other starts from the result, repeatedly simplifies it until it can be proved from known premises. The former is bottom-up; the latter is top-down.

Litex works bottom-up: it derives new facts from known conditions, and the source states results. Every already verified fact can be used by later reasoning.

The usual mental flow of writing Litex is to ask: “From the facts we already have, what new facts can we obtain?” After enough knowledge accumulates, we gradually approach the goal. Even if we never obtain the desired conclusion, the intermediate steps remain valuable and may be usable in other problems.

Lean's typical interaction is backward and top-down: first fix a goal, then decompose it into subgoals solved by hypotheses or theorems, and finally assemble a proof term.

The usual mental flow of writing Lean asks “how can the goal be reduced to known conditions?”; Litex often asks “what facts can be established from known conditions?” The difference is the default direction, not the logical standard.

<a id="two-directions"></a>

<details>
<summary><strong>Small example: top-down and bottom-up writings of the same algebraic equality</strong></summary>

This example shows two directions of progress for the same equality. Lean starts from the goal; each `rw` specifies a fact, a matching direction, and a replacement:

```lean
-- Using facts from the local context.
example (a b c d g f : ℝ) (h : a * b = c * d) (h' : g = f) :
    a * (b * g) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

Litex writes an equality chain from `a * (b * g)` to `c * (d * f)`. This left-to-right orientation verifies in the current kernel:

```litex
claim:
    ?forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    a * (b * g) = (a * b) * g = (c * d) * g = (c * d) * f = c * (d * f)
```

The chain reassociates the product, substitutes `a * b = c * d`, substitutes `g = f`, and reassociates again. Lean specifies how to rewrite the goal next; Litex writes the facts that should hold along the way, and the kernel searches for grounds of adjacent equalities.

</details>

<details>
<summary><strong>Place in the design space: forward proof is not Litex's invention</strong></summary>

Mizar, Isar, ACL2, and Naproche already support forward text, theorem accumulation, or stepwise checking, so “bottom-up” is not unique to Litex. Litex tests a combination: ordinary facts automatically trigger local verification, extend the context when they succeed, and keep accepted or stopped paths visible for humans or AI to inspect and repair; explicit proof structure is written only when ordinary verification is insufficient. A fuller comparison appears in Section 1's summary “Litex and Naproche—Similar Goals, Different Core Interfaces.”

</details>

<a id="interaction-loop"></a>

## 4. Humans, AI, and Litex Advance Proofs Together

The previous sections explained what Litex leaves behind after a definition or fact is executed. Larger mathematical development still needs another layer: how humans and AI use these records to continue constructing, while keeping mathematical intent, candidate proposals, verification decisions, and source under maintenance separate.

Litex starts from set-theoretic objects and membership, lets fact-oriented source grow a verified context from the bottom up, and directly outputs structured verification results rather than only a final true/false label. It is this design combination that constitutes Litex's distinctiveness and makes the division of labor in building a `human–AI–Litex loop` very clear:

```text
Human proposes a mathematical problem and an intended solution
                         ↓
AI splits the problem and solution into ordered fragments
                         ↓
              ┌──── fragment formalization loop ────┐
              │                                     │
              ▼                                     │
AI writes the current fragment as Litex code        │
                         ↓                          │
Litex structured verification result                │
   ├─ success                                       │
   │     → record this code                         │
   │     → record how Litex ran it                  │
   │     → go to the next fragment ─────────────────┘
   └─ RolledBack
         → evidence-based diagnosis
         → repair the same fragment and try again
                         ↓
All successful fragments are joined in order → the problem is solved and formalized
                         ↓
Human experts perform a basic check
                         ↓
These Litex programs become building blocks for later problems
```

> Any single Litex feature can find a shadow in some historical formal language: for readability, Naproche has a writing format very close to textbooks; based on set theory? Mizar is; other formal languages with rich ecosystems are many. Litex gathers strengths from many languages into its own design style, so that it can face a broad non-specialist user population and adapt to the needs of the AI era.

> Beyond mathematics, other industries with strong demand for trustworthy reasoning—such as AI safety and software verification—have shown interest in such a human–AI–Litex loop.

In the fragment formalization loop, the execution flow advances in source order; each round handles only one definition, theorem, or small proof fragment. AI proposes Litex code for that fragment; Litex returns a structured verification result that decides whether the round can continue. On success, the result leaves two things at once: the accepted source for this fragment, and a run record of how the code was checked and on what grounds it holds—without the latter, AI would not know what to trust next or what to repair; with it, successful fragments can become accepted premises for later fragments, and failed fragments can be diagnosed precisely without polluting the context. When all fragments succeed and join, the problem is both solved and formalized; human experts then perform a basic check. Only Litex code that passes review, together with its run records, becomes reusable mathematical building blocks for later problems. In other words, what drives the loop forward is not AI's fluent phrasing, but Litex's every checkable, replayable, handoff-ready output.

Therefore what Litex leaves behind is not only final reusable `.lit` source. It also preserves AI's attempts during formalization themselves: what was right, what was wrong, how it was right, and how it was wrong. That experience outside the source is equally essential—without it, later readers would see only a finished proof; with it, humans and AI can revisit the construction path, reuse repair methods, and turn one solution into learnable formalization experience.

**What readers should see on success.** When this human–AI–Litex loop truly runs, readers need not first become proof-assistant experts to see directly that textbook-style definitions and theorems can be read and written by mathematical intent and checked by machine; that local failure stops at the current fragment with repairable evidence and does not pollute the accepted context; and that successful fragments, joined in order, leave reusable `.lit` source and replayable run records for later problems. Machine success still requires a basic human check—that is the loop’s end criterion, not a side decoration.

<details>
<summary><strong>Example: walking one fragment formalization loop by the flowchart</strong></summary>

Below is a small standalone example whose steps correspond one-to-one with the flowchart above. It is deliberately incomplete; it is only meant to make the loop itself visible: first define language, then verify what can be derived under those definitions.

<a id="convergence-example"></a>

**1. Human proposes a mathematical problem and an intended solution**

> First define sequence convergence: for every positive error `ε`, there exists a position `N` after which every term is close enough to the limit. Then prove: if `{s(n)}` converges to `a`, then `{c * s(n)}` converges to `c * a`.

**2. AI splits the problem and solution into ordered fragments**

For this problem, AI might first split it into, for example:

1. Define “eventually close enough,” a predicate defined with `prop`
2. Define “convergence,” a predicate defined with `prop`
3. Write and prove a `thm`: scalar multiplication preserves convergence

**3. Fragment formalization loop: the first two fragments succeed—definitions enter the context**

AI first submits two definitions; Litex returns success. That leaves this source, together with a record of how Litex ran it. The accepted context grows, and later theorem fragments can unfold by definition.

```litex
# "Eventually close enough": from N0 onward, every term lies within error epsilon.
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            abs(s(n) - a) < epsilon

# "Converges to a": for every positive error there exists such an N0.
prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}
```

**4. Failure and repair in the same loop: proving that scalar multiplication preserves convergence**

AI first tries to obtain convergence of the new sequence by `by def` without constructing the `forall / exist` structure. Litex returns failure and rolls back:

```json
{
  "kind": "run",
  "success": false,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": false,
      "statement": "...",
      "why_failed": {
        "phase": "search_proof",
        "goal": "$converges_to(fn(n N) R {c * s(n)}, c * a)"
      },
      "stores": [],
      "infers": []
    }
  ]
}
```

The accepted context is unchanged. The record explains: the definition supplies the shape to prove, not a ready-made conclusion; one must first obtain and deliver a suitable `N0` for each `epsilon`. AI repairs only this fragment:

> **Migration example:** Current `src/` checking stops at `def_thm` (`thm`). This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
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
                    abs(c * s(n) - c * a) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < epsilon
                    abs(fn(k N) R {c * s(k)}(n) - c * a) < epsilon
            by def $is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)
    by def $converges_to(fn(n N) R {c * s(n)}, c * a)
```

Litex checks again and succeeds. That again leaves source and a run record.

**5. All successful fragments join → the problem is solved and formalized**

Successful fragments are joined in order into one continuous Litex development: first definitional language, then a theorem under those definitions. Final source contains only the successful prefix; failed attempts remain recorded to explain repairs, but do not become mathematical premises.

**6. Human experts perform a basic check**

Experts check whether the intent is still “define convergence and prove that scalar multiplication preserves it,” whether the `prop`s are faithful to the analysis definitions, and whether the estimates are credible. Machine success does not waive review.

**7. These Litex programs become building blocks for later problems**

After review, this convergence interface and scalar-multiplication theorem can be cited by later problems such as limit algebra and continuous functions. What remains is not only that one proof, but a reusable formal foundation and experience of “what was right and what was wrong.”

</details>

<a id="compatibility"></a>

## 5. Connect to Lean for Independent Rechecking and Mathlib Interoperability (Experimental)

**Lean rechecking**: the intended independent checking path. Earlier experimental artifacts remain in `lean/`; the current build does not expose their compiler.

Litex can work independently; it has syntax, a runtime, and a verification kernel. If you trust that the Litex kernel has no bugs, it can check well-definedness and facts and give feedback without compiling to Lean.

But for large mathematical systems, Lean has unmatched advantages: a mature Lean/Mathlib ecosystem, rich reusable mathematical objects and theorem libraries, and a small, auditable kernel. Litex hopes to connect to Lean's ecosystem so that the Lean community can also benefit from Litex, and so that Litex can provide Lean with a more readable, more writable mathematical interface in some mathematical directions.

Independent Lean checking could reduce reliance on Litex’s verifier implementation for supported proofs, provided the translation preserves the original statement and the emitted proof is checked by Lean without proof holes. This is a verification goal, not a guarantee supplied by the current build.

> **Current build:** `Cargo.toml` registers the `litex` binary, and `src/lib.rs` has no compiler module. The retained `lean/stmt_result_to_lean_compiler.sh` wrapper names a missing Cargo binary. The example below records an earlier experiment; it has not been regenerated or Lean-checked against current `src/`.

<details>
<summary><strong>Example: how Litex code compiles to Lean</strong></summary>

Compiling Litex to Lean and connecting to Mathlib-style Lean code goes through the following process:

`Litex source → Litex verification → ToLean compilation → Lean kernel recheck → handwritten adapter → Mathlib theorem`

> Compiling Litex to Lean is much like compiling C to assembly. We know assembly looks like gibberish because the source writes many memory addresses; both allocating a new address and using it require writing the address explicitly. Lean code names every fact, and calling a corresponding fact also requires attaching the name explicitly. When the Litex kernel processes Litex code, it maintains such a fact table for the user and, during verification, searches that table by the predicate name of each atomic fact as key, to help prove what is currently to be proved (why this works, and why Lean cannot easily copy the same default mechanism, see Section 1). That search branches widely (Litex has hundreds of builtin verification rules) but is not deep (each verification rule is straightforward; any builtin rule can be compiled into several Lean tactics).

Example: we want to prove that the sum of the first `n` positive odd numbers is `n^2`. We first write Litex source:

> **Migration example:** Current `src/` checking stops at `internal_bug: name n is already bound in an enclosing parse scope`. This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
have fn kth_odd(k Z) Z = 2 * k - 1

forall n Z:
    n >= 1
    =>:
        sum(1, n, kth_odd) $in Z

forall n Z:
    n^2 $in Z

thm sum_first_odds:
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) = n^2
    by induc n from 1:
        ? sum(1, n, kth_odd) = n^2

        ? from n = 1:
            kth_odd(1) = 2 * 1 - 1 = 1
            sum(1, 1, kth_odd) = kth_odd(1) = 2 * 1 - 1 = 1 = 1^2

        ? induc:
            kth_odd(n + 1) = 2 * (n + 1) - 1
            sum(1, n + 1, kth_odd) = sum(1, n, kth_odd) + kth_odd(n + 1) = n^2 + kth_odd(n + 1) = n^2 + (2 * (n + 1) - 1) = (n + 1)^2
```

Compiled to Lean (different Litex versions may generate different output)

```lean
-- Generated by StmtResultToLeanCompiler from main.lit. DO NOT EDIT.
import Litex

set_option linter.style.nameCheck false

namespace __Compiler_main

noncomputable def kth_odd : Litex.Fn Litex.Z Litex.Z :=
  { call := fun {__alpha} (__arg : __alpha) __arg_in => (((2 : ℤ) * Litex.In.rep __arg __arg_in) - (1 : ℤ)), callOwn := fun (__arg : ℤ) => (((2 : ℤ) * __arg) - (1 : ℤ)) }

theorem __fact0 : Litex.In kth_odd (Litex.fnSet Litex.Z Litex.Z) := by
  exact Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd

theorem __fact1 : Litex.Same kth_odd ({ call := fun {__alpha} (__arg : __alpha) __arg_in => (((2 : ℤ) * Litex.In.rep __arg __arg_in) - (1 : ℤ)), callOwn := fun (__arg : ℤ) => (((2 : ℤ) * __arg) - (1 : ℤ)) } : Litex.Fn Litex.Z Litex.Z) := by
  unfold kth_odd
  exact Litex.Same.refl ({ call := fun {__alpha} (__arg : __alpha) __arg_in => (((2 : ℤ) * Litex.In.rep __arg __arg_in) - (1 : ℤ)), callOwn := fun (__arg : ℤ) => (((2 : ℤ) * __arg) - (1 : ℤ)) } : Litex.Fn Litex.Z Litex.Z)

theorem __fact2 :
    ∀ (__p1 : ℤ) (__domain1 : Litex.Le (1 : ℂ) (((__p1) : ℂ))), Litex.In (Litex.sum (1 : ℤ) __p1 kth_odd) Litex.Z := by
  intro n __domain_f17
  have __infer2_0 : Litex.Lt (0 : ℂ) (((n) : ℂ)) := Litex.Lt.transLe (Litex.OrderBridge.ltOfComplexReals (show (0 : ℝ) < (1 : ℝ) by norm_num)) (__domain_f17)
  have __prior2_0 : Litex.In (Litex.sum (1 : ℤ) n kth_odd) Litex.Z := Litex.In.own Litex.Z ((Litex.sum (1 : ℤ) n kth_odd))
  exact __prior2_0

theorem __fact3 :
    ∀ (__p1 : ℤ), Litex.In (((((__p1) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) Litex.Z := by
  intro n
  have __prior3_0 : Litex.In (((((n) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) Litex.Z := Litex.Rules.complexIntPowNatInZ (n) (2 : ℕ)
  exact __prior3_0

theorem sum_first_odds :
    ∀ (n : ℤ) (__domain_f48 : Litex.Le (1 : ℂ) (((n) : ℂ))),
      Litex.Same (Litex.sum (1 : ℤ) n kth_odd) (((((n) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := by
  intro n __domain_f48
  have __step4_29 : ∀ (__p1 : ℤ) (__domain1 : Litex.Le (1 : ℂ) (((__p1) : ℂ))), Litex.Same (Litex.sum (1 : ℤ) __p1 kth_odd) (((((__p1) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := by
    intro __target_value __domain1
    have __target_ge_start_real : (((1 : ℤ)) : ℝ) ≤ (__target_value : ℝ) := by
      simpa [Litex.Le, Litex.OrderValue] using __domain1
    have __target_ge_start : (1 : ℤ) ≤ __target_value := by
      exact_mod_cast __target_ge_start_real
    exact Litex.Rules.integerInductionFrom (motive := fun __induction_value : ℤ => Litex.Same (Litex.sum (1 : ℤ) __induction_value kth_odd) (((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)) (by
    have __step4_2 : (Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ))) ∧ (Litex.Same (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) (1 : ℂ)) := by
      exact ⟨Litex.Same.trans ((by
      unfold Litex.fnApplyCarrier kth_odd
      exact Litex.Same.intSubComplex (Litex.Same.intMulComplex (Litex.Same.intComplexOfEq (z := (2 : ℤ)) (by norm_num)) (Litex.Same.intComplexOfEq (z := ((1 : ℤ))) (by norm_cast))) (Litex.Same.intComplexOfEq (z := (1 : ℤ)) (by norm_num)))) (Litex.Same.refl (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ))), Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])⟩
    have __infer4_3 : Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (1 : ℂ) := Litex.Same.trans ((__step4_2).1) ((__step4_2).2)
    have __step4_4 : (Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ))) ∧ (Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ))) ∧ (Litex.Same (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) (1 : ℂ)) ∧ (Litex.Same (1 : ℂ) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) := by
      exact ⟨Litex.Same.trans (Litex.Same.symm (Litex.Same.symm (Litex.Same.trans (Litex.Rules.integerRangeSumSingleOwn (1 : ℤ) kth_odd) ((__step4_2).1)))) (Litex.Same.symm ((by
      unfold Litex.fnApplyCarrier kth_odd
      exact Litex.Same.intSubComplex (Litex.Same.intMulComplex (Litex.Same.intComplexOfEq (z := (2 : ℤ)) (by norm_num)) (Litex.Same.intComplexOfEq (z := ((1 : ℤ))) (by norm_cast))) (Litex.Same.intComplexOfEq (z := (1 : ℤ)) (by norm_num))))), ⟨(__step4_2).1, ⟨(__step4_2).2, Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])⟩⟩⟩
    have __infer4_5 : Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) := Litex.Same.trans ((__step4_4).1) ((__step4_4).2.1)
    have __infer4_6 : Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (1 : ℂ) := Litex.Same.trans (Litex.Same.trans ((__step4_4).1) ((__step4_4).2.1)) ((__step4_4).2.2.1)
    have __infer4_7 : Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans (Litex.Same.trans ((__step4_4).1) ((__step4_4).2.1)) ((__step4_4).2.2.1)) ((__step4_4).2.2.2)
    have __infer4_8 : Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans ((__step4_4).2.1) ((__step4_4).2.2.1)) ((__step4_4).2.2.2)
    have __infer4_9 : Litex.Same (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans ((__step4_4).2.2.1) ((__step4_4).2.2.2)
    have __infer4_10 : Litex.In (1 : ℂ) Litex.RPos := (Litex.In.congr ((__step4_4).2.2.2) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_11 : Litex.Positive (1 : ℂ) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_10)))
    have __infer4_12 : Litex.In (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) Litex.RPos := (Litex.In.congr (__infer4_7) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_13 : Litex.Positive (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_12)))
    have __infer4_14 : Litex.In (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) Litex.RPos := (Litex.In.congr (__infer4_8) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_15 : Litex.Positive (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_14)))
    have __infer4_16 : Litex.In (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) Litex.RPos := (Litex.In.congr (__infer4_9) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_17 : Litex.Positive (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_16)))
    exact (by simpa using (__infer4_7))) (fun (__induction_value : ℤ) (__induction_ge_start : (1 : ℤ) ≤ __induction_value) (__induction_hypotheses : Litex.Same (Litex.sum (1 : ℤ) __induction_value kth_odd) (((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)) => by
    have __infer4_18 : Litex.Lt (0 : ℂ) (((__induction_value) : ℂ)) := Litex.Lt.transLe (Litex.OrderBridge.ltOfComplexReals (show (0 : ℝ) < (1 : ℝ) by norm_num)) ((by
      have __induction_ge_start_real : (((1 : ℤ)) : ℝ) ≤ (__induction_value : ℝ) := by
        exact_mod_cast __induction_ge_start
      simpa [Litex.Le, Litex.OrderValue] using __induction_ge_start_real))
    have __infer4_19 : Litex.In (Litex.sum (1 : ℤ) __induction_value kth_odd) Litex.RPos := (Litex.In.congr (__induction_hypotheses) Litex.RPos).mpr (Litex.Rules.positiveIntegerRationalPowInRPos (__induction_value) (2 : ℤ) (__infer4_18) (by norm_num))
    have __infer4_20 : Litex.Positive (Litex.sum (1 : ℤ) __induction_value kth_odd) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_19)))
    have __step4_21 : Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))) (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ)) := by
      exact Litex.Same.trans ((by
      unfold Litex.fnApplyCarrier kth_odd
      exact Litex.Same.intSubComplex (Litex.Same.intMulComplex (Litex.Same.intComplexOfEq (z := (2 : ℤ)) (by norm_num)) (Litex.Same.intComplexOfEq (z := ((__induction_value + (1 : ℤ)))) (by norm_cast))) (Litex.Same.intComplexOfEq (z := (1 : ℤ)) (by norm_num)))) (Litex.Same.refl (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ)))
    have __step4_22 : (Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))))) ∧ (Litex.Same ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))))) ∧ (Litex.Same ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ)))) ∧ (Litex.Same ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)) := by
      exact ⟨Litex.Rules.integerRangeSumSplitLastOwn (1 : ℤ) __induction_value kth_odd ((by simpa [Litex.Le, Litex.OrderValue] using ((by
      have __induction_ge_start_real : (((1 : ℤ)) : ℝ) ≤ (__induction_value : ℝ) := by
        exact_mod_cast __induction_ge_start
      simpa [Litex.Le, Litex.OrderValue] using __induction_ge_start_real)))), ⟨Litex.Same.intCastAddComplex (__induction_hypotheses) (Litex.Same.intComplex ((Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))))), ⟨Litex.Same.addCongrRightInt (Litex.Same.refl ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ))) (__step4_21), Litex.Same.trans (Litex.Same.refl (((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))))) (Litex.Same.trans (Litex.Same.ofEq ((show ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) = ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) from (by norm_cast <;> ring_nf)))) (Litex.Same.symm (Litex.Same.refl (((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)))))⟩⟩⟩
    have __infer4_23 : Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) := Litex.Same.trans ((__step4_22).1) ((__step4_22).2.1)
    have __infer4_24 : Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) := Litex.Same.trans (Litex.Same.trans ((__step4_22).1) ((__step4_22).2.1)) ((__step4_22).2.2.1)
    have __infer4_25 : Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans (Litex.Same.trans ((__step4_22).1) ((__step4_22).2.1)) ((__step4_22).2.2.1)) ((__step4_22).2.2.2)
    have __infer4_26 : Litex.Same ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) := Litex.Same.trans ((__step4_22).2.1) ((__step4_22).2.2.1)
    have __infer4_27 : Litex.Same ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans ((__step4_22).2.1) ((__step4_22).2.2.1)) ((__step4_22).2.2.2)
    have __infer4_28 : Litex.Same ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans ((__step4_22).2.2.1) ((__step4_22).2.2.2)
    exact (by simpa using (__infer4_25))) __target_value __target_ge_start
  have __c4_0 : Litex.Same (Litex.sum (1 : ℤ) n kth_odd) (((((n) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := (by
    simpa [Litex.In.rep, Litex.fnApply, Litex.fnApplyOwn, Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using (__step4_29 n (by
    simpa [Litex.In.rep, Litex.fnApply, Litex.fnApplyOwn, Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using (__domain_f48))))
  exact __c4_0

end __Compiler_main

```

The generated code is Lean code, but under Litex's semantics. We add a small adapter that bridges Litex's representation to Mathlib:

```lean
import Generated

/-! The handwritten interface from generated Litex evidence to native Mathlib. -/

namespace Adapter

/-- Export the generated theorem as ordinary Mathlib equality. -/
theorem sumFirstOddsNative
    (n : ℤ)
    (oneLeN : (1 : ℤ) ≤ n) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2 := by
  have generated :=
    __Compiler_main.sum_first_odds n
      (Litex.OrderBridge.leOfComplexReals (by exact_mod_cast oneLeN))
  have exactComplexEq :
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
        ((n ^ 2 : ℤ) : ℂ) := by
    calc
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
          ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) :=
        Litex.Same.intComplexEq generated
      _ = ((n ^ 2 : ℤ) : ℂ) := by norm_cast
  exact_mod_cast exactComplexEq

end Adapter

```

After bridging, the conclusion can use Mathlib's native interface:

```lean
import Adapter

/-- A native theorem whose statement is entirely independent of Litex. -/
theorem firstHundredPositiveOddIntegersSum :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  exact Adapter.sumFirstOddsNative 100 (by norm_num)

```

Litex can therefore be viewed as a more readable, more understandable front-end language for Lean. Users write Litex code, understand the whole proof process from the Litex code, then compile to Lean to ensure verifiability and connect to the Mathlib ecosystem. I believe this is a direction well worth exploring.

</details>

<a id="ecosystem-role"></a>

## 6. From Language to Ecosystem: The Role Litex Aims to Play

Taken together, the designs make Litex hope to become infrastructure on which humans and AI jointly produce and use checkable reasoning.

**Litex faces humans and AI: it is both a readable reasoning front end and a trustworthy-reasoning data production layer, and it tries to connect to the existing ecosystem through Lean/Mathlib.** It also hopes to serve AI, engineers, and practitioners in other domains.

The mathematicians' workflow of the future will involve AI and humans working together to produce a proof and then generating formal code so that its correctness can be checked. That formal code may be Lean or Litex. Litex hopes to become a more readable front end to Lean, lowering the barrier to reading and writing formal code.

Earlier sections showed that this role is not a simple sum of several features. Set-theoretic objects, fact-oriented source, a bottom-up growing verified context, minimal syntax, expression close to natural mathematics, and structured verification results enter the same protocol together, so that both mathematics itself and the construction evidence of mathematics can be preserved.

| Ecosystem role | Practical outcomes Litex hopes to produce |
| --- | --- |
| Front end for readable reasoning | Mathematical objects, conditions, intermediate facts, and conclusions that humans can audit directly |
| Production layer for trustworthy reasoning data | Machine-checked facts and verification sources, clear stopping boundaries, and explicitly marked trust boundaries |
| Access layer to the existing ecosystem | Designed from the start for Lean compilation and rechecking (Section 5, experimental); earlier Lean proof artifacts preserve experimental coverage, but the current build has no compiler entrypoint; plus newly written Lean/Mathlib adapters, cleanly separated and authored by AI or humans |
| Proofs → executable code (experimental) | Turn checked computational fragments into runnable Python / C (Section 6.1) |

Of course, Litex at this stage is more like a `proof of an idea`. Even though it already has hundreds of thousands of lines of code, exploration of its place in industry upstream and downstream remains scarce. That is what Litex's next stage will focus on: how to turn zero-to-one original innovation into one-to-ten early value realization. Friends interested in Litex can contact litexlang@outlook.com .

<details>
<summary><strong>Litex's ecological niche</strong></summary>

A supply–demand relationship for formal languages is inevitable. Language design is usually led by one or two people: design, engineering, and iteration proceed together; keeping the design circle small is what helps preserve consistency—this is almost the normal pattern for any programming language. But actually building a formal language is enormous engineering: kernel, rules, standard library, toolchain, documentation, and ecosystem are far beyond what the same one or two people could carry at once under traditional labor alone. Without AI assisting implementation and iteration, a project like Litex—whose design surface must stay small while its engineering surface is huge—was almost impossible to land; it is AI's development that makes such projects tryable.

At the same time, new industries are raising demand for formalization. Programming languages rarely become popular in a vacuum. They usually arise where new technical capability meets new social demand: Fortran with mainframe computing power and high-performance needs; C and Unix shaping each other for systems programming; JavaScript and Java with the internet era's front- and back-end development; Python and CUDA with rapid AI-framework iteration and high-performance compute underneath. Lean's latest wave likewise coincides closely with AI for Math's demand for reliable formalization.

What Litex seeks is precisely the next scene that the AI era is incubating and that is still hard to name accurately. AI will keep generating large volumes of candidate reasoning, and new knowledge work will therefore need cheaper checking, explanation, organization, and reuse. Whether the formal-language field can catch this wave is a question the industry needs to face together. I believe such a scene should appear soon.

</details>

<a id="executable-code"></a>

### 6.1 Compiling Proofs to Executable Code (Python / C) (Experimental)

Litex is also experimenting with a second compilation route: turn (parts of) a verified proof into runnable code—today mainly supported numeric definitions and `algo` fragments into Python or C. The point is not “export a whole theorem library,” but: once a computational step is checked in Litex, the same writing can become executable code you can run.

This route is deliberately narrow and experimental. It is not a whole-Litex-to-Python/C compiler; coverage is limited to extractable definitions. For the CLI surface, see `-extractpython` / `-extractc` in the CLI docs.

<details>
<summary><strong>Sketch: Newton step for √2 → Python / C</strong></summary>

The same Litex proof used for scientific computing can become executable code. For example, one Newton step toward √2:

> **Migration example:** Current `src/` checking stops at `parse_error: undefined name newton_sqrt_two_step`. This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
have fn newton_sqrt_two(x R+) R+ = (x + 2 / x) / 2

claim:
    ? forall x R+:
        newton_sqrt_two_step(x) = newton_sqrt_two(x)
    newton_sqrt_two_step(x) = (x + 2 / x) / 2 = newton_sqrt_two(x)

algo newton_sqrt_two_step(x R) R by cases:
    case x = 0: 1
    case x != 0: (x + 2 / x) / 2
```

To Python:

```python
def newton_sqrt_two_step(x):
    if x == 0.0:
        return 1.0
    elif x != 0.0:
        return ((x + (2.0 / x)) / 2.0)
    raise AssertionError("unreachable verified Litex cases")
```

To C:

```c
#include <stdlib.h>

double newton_sqrt_two_step(double x) {
    if (x == 0.0) {
        return 1.0;
    }
    else if (x != 0.0) {
        return ((x + (2.0 / x)) / 2.0);
    }
    abort();
}
```

</details>

<a id="reasoning-direction"></a>

<a id="conclusions"></a>

## 7. The Art of Seeking What Is Different

<!-- This passage is a bit more idealistic. In the AI era, everyone focuses too much on pragmatism and easily overlooks the long-term influence of a native, innovative, distinctive new solution. Whether in mathematics or in any science, people encourage different angles and different solutions to the same problem. Such different viewpoints are often the true sources of breakthroughs in the history of science, and may ultimately bring greater gains in effectiveness. -->

In the starlit history of science, new perspectives and new answers to the same problem have often greatly driven the development of the original field, and even given birth to entirely new disciplines. In an AI era that prizes efficiency above all, even in a discipline as known for long-termism as mathematics, we can still easily get lost in local optima of racing to publish and climbing leaderboard publicity, and overlook rethinking first principles and original innovation.

This does not mean denying Lean's enormous success. With its elegant type theory, reliable kernel, and rich Mathlib ecosystem, Lean has shown that mathematics can be engineered with rigor. Litex wants to ask a different question: under the premise that it was designed from the start to compile to Lean for kernel rechecking—with earlier experimental artifacts retained and current compiler integration still absent—can a formal language adopt an interface closer to natural mathematics, so that source, verification process, and mathematical dependencies are easier for people to understand, write, and join? This is not an attempt to find an answer that replaces Lean, but to add a direction worth testing to the design space of formal languages.

Of course, Litex may not become the only path, and it need not become the only path. Litex hopes the world will be better because of mathematics, and that the mathematical world will be better because of formal languages. I believe that such “nonstandard solutions” as Litex have long-term value—again as a personal judgment, not as an authoritative claim.

<details>
<summary><strong>A note from the author</strong></summary>

I am Jiachen Shen (沈嘉辰), a mathematics PhD student at Fudan University. Lean showed me that mathematics and programming can meet in a real language. Litex explores whether formal source can follow more closely the mental flow of solving mathematical problems.

The author of Litex has spent about two years on this project—almost every day from morning to night—entirely as a volunteer, with no material return. The hope is simply to make some friends through it, and to offer Math for AI one more idea. It is an open-source project: [golitex](https://github.com/litexlang/golitex). If you strongly oppose Litex’s existence or design, serious discussion is welcome—but please do not flame. The author believes he has already done what he can to lay the work open for others to see, and sincerely hopes the Math for AI field keeps getting better.

</details>

<a id="special-thanks"></a>

### Special Thanks

Litex is created and maintained by Jiachen Shen and the Litex team. Special thanks to Wei Lin, Siqi Sun,
Peng Sun, Chenxuan Huang, Yan Lu, Sheng Xu, Keyao Zhu and Zhaoxuan Hong for their support and advice on the project.

### Related Links

1. To try examples directly and view Litex-generated output and knowledge graphs, visit [litexlang.com](https://litexlang.com).

2. For kernel implementation, see the [golitex repository](https://github.com/litexlang/golitex).

Note: the current repository retains checked results, experiments, and unfinished work at once. *Public visibility is not a claim of completion*; capabilities should be judged by tests, dated status, trust boundaries, and known limitations.

### Native theorem interfaces and diagnostics (2026-10-02)

The 25 reserved legacy theorem names now have native contracts in
`src/execute/execute_by_stmt/builtin_thm/`. The theorem-release path checks
requirements and conclusion well-definedness before committing conclusions to
the surrounding context, and reports the actual
failed stage and premise. Complex arithmetic containing `i` is handled by
calculation. Indexed constructions require a nonempty index set. These changes
preserve the AST and Runtime/ExecEnv contracts; explicit equality chains remain
the authoring route for definition endpoints. See the Manual's builtin table
for supported argument shapes and the axiom-of-choice provenance.

<a id="overview-readers"></a>

## Appendix: Programming, Mathematics, and Formalization with Litex

This section draws on the experience of Lean users, mathematicians, programmers, and readers in other knowledge domains to discuss the knowledge and perspectives Litex may offer. You can choose the parts that interest you, or return to the [five main threads](#overview-spine) to continue exploring the language design.

### For Lean users

Why another formal language?

When I first encountered Lean, I was astonished: mathematics could be written as code, and proofs could be checked by a machine! The very idea of turning mathematics into code was exciting, and it led me to think about how I would want to use a formal language.

As I learned, a few questions took shape. What if I could simply write `1 + 1 = 2`, without first writing `example` and then `by ...`? What if, after defining oddness, I could write `$odd(13)` and let the language check it against the definition? What if, already knowing that all humans are mortal and that Socrates is human, I could write that Socrates is mortal without explicitly citing the universal premise again?

These questions gradually came together as a basic idea behind Litex: **the user writes each mathematical step; the formal language finds and explains why that step holds.** Calculation, definitions, and known premises supply different kinds of grounds, while the user's way of participating stays the same: writing the fact that should hold next.

The author still supplies the key mathematical constructions and the route of the argument. The language handles as much of the local verification between steps as it can and presents the grounds it finds. Many of Litex's simplifications and conventions follow this division of work.

This division of work leads to several basic starting points for Litex:

1. On the user side, return to sets, elements, functions, and relations—rather than crossing type engineering first.
2. Source by default writes *what to prove*; the kernel searches for *how*.
3. Common facts need not be named and cited everywhere, and a readable proof trace is produced.
4. When the semantics are plain enough, the result should compile to Lean or another system that can represent set theory, then be independently rechecked by that system’s kernel.

```text
Lean:  proposition → proof goal → tactic refinement → proof term → kernel check
Litex: objects and facts → kernel checks and searches for grounds → verified facts extend the context
```

A related difference sits one layer below tactics. Lean’s default surface, via dependent type theory, gathers mathematical objects, propositions, proofs, and types into one term/type universe—so values and evidence are often packed together (as in the subtype example below). Litex keeps those categories apart on the user surface: objects, facts, and statements stay separate, closer to how everyday mathematics already talks. That is not a claim about proof power; it is a claim about what the source asks you to see first. *Litex’s “type” feel is closer to Python; Lean’s is closer to Rust.*

Modern formal languages with Lean as a leading representative laid an irreplaceable foundation for AI for Math and the “engineering of mathematics.” Yet no matter how AI develops, people who can master Lean, type theory, and its engineering stack may still remain a minority. Litex does not try to replace Lean; it explores another formalization perspective: letting more people write, check, and understand rigorous mathematical knowledge directly. Litex and Lean take nearly *inverse* defaults—one source leans toward *how*, the other toward *what*; one accumulates conclusions from conditions, the other simplifies the conclusion until it matches the conditions—turning over the large half of a formal system that used to stay hidden behind the interface. People with different habits of thought can each find the language that fits them.

*Here sits a division of labor that is easy to underestimate, yet essential: **the language helps you prove; the user says what to prove**—not the reverse, where the user must first learn how to prove and then encode those proof steps into the source. So Litex output is not merely pass/fail: it tells you the mathematical grounds behind each statement. When you read Litex source, you are reading what should hold; from the output, you also read the mathematical principles that support each line—beyond the source text itself. Lean is usually the other way around: the source writes how to prove, and Lean’s output tells you what you have proved.*

If you want to understand Litex’s design, the best way is to walk the path yourself: start from everyday mathematics, notice the interface mismatch, return *what* to people and hand *how* to the kernel. What you arrive at may not be called Litex; but you will see why it almost had to grow this way.

Lean is a major reference point for Litex. An earlier compiler experiment explored translating Litex evidence to Lean, and the retained artifacts illustrate the intended connection. The current `src/` and Cargo targets do not build that compiler. Treat a readable Lean frontend as a research direction, not as a promise that current Litex programs already compile to Lean.

This ease of use has an engineering cost: Litex's verifier must understand common mathematical objects and proof shapes, check well-definedness, give grounds for accepted facts, and leave records that later statements can use. Local matching indexed by predicate name saves authors from naming many grounds by hand and may keep supported local checks light; claims about speed or memory still need benchmarks on matched tasks with comparable libraries. The difficulty is not the size of any one rule, but how rules interact with other mathematical objects, logical forms, and failure feedback.

The Lean comparison must also distinguish two paths: proofs are elaborated from surface syntax into core expressions that the kernel checks, while compiler IR serves executable programs. Litex puts more mathematics-specific rules into its own verification system, increasing the implementation and auditing burden. Earlier compiler experiments show a route for handing evidence to Lean, but that compiler is not wired into the current build. Independent Lean rechecking remains a goal rather than a current guarantee.

<details>
<summary><strong>Lean–Litex comparison examples</strong></summary>

Below are three representative Lean–Litex side-by-side examples. For table compactness, Lean examples omit `import` lines. They compare default interfaces, not proof length, and do not claim that the two languages have identical capability boundaries:

<table>
<thead>
<tr><th>Litex example</th><th>Lean example</th></tr>
</thead>
<tbody>
<tr>
<td><strong>Direct fact: given x = 2</strong><pre><code>forall x R:
    x = 2
    =&gt;:
        x + 1 = 3
        x^2 = 4</code></pre></td>
<td><strong>The same fact</strong><pre><code>example (x : ℝ) (h : x = 2) :
    x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩</code></pre></td>
</tr>
<tr>
<td><strong>Conditional function domain</strong><pre><code>forall x {y R: y &gt; 0}:
    x &gt; 0

have fn positive_successor(x R: x &gt; 0) R = x + 1

positive_successor(1) = 2</code></pre></td>
<td><strong>Carry the condition with a subtype</strong><pre><code>def positiveSuccessor
    (x : {y : ℝ // y &gt; 0}) : ℝ := x.val + 1

example : positiveSuccessor ⟨1, by norm_num⟩ = 2 := by
  norm_num [positiveSuccessor]</code></pre></td>
</tr>
<tr>
<td><strong>Intersection preserves subset</strong><pre><code>forall s, t, u set:
    s $subset t
    =&gt;:
        intersect(s, u) $subset intersect(t, u)</code></pre></td>
<td><strong>Unfold set definitions and prove pointwise</strong><pre><code>example {alpha : Type*} (s t u : Set alpha) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩</code></pre></td>
</tr>
</tbody>
</table>

</details>

<details>
<summary><strong>Two barrier examples unfolded</strong></summary>

The next two examples show two sources of the complexity tax. They do not compare mathematical ability; they only ask: from “I understand” to “I can formalize,” what is still missing?

1. **Tool-use barrier**: a user already understands a mathematical fact, yet may not know how to write it into a formal system.
2. **Expression barrier**: the way mathematics is written in a formal system may differ from everyday mathematical expression we are used to.

Start with the tool barrier. Often the mathematics itself is already simple—for example `1 + 2 = 3`, which a child can write, or a polynomial identity. What stalls inside the formal system is often not “do I understand the mathematics,” but whether one remembers which tactic or lemma to call.

Litex:

```litex
1 + 2 = 3

forall a, b R:
    (a + b)^2 = a^2 + 2 * a * b + b^2
```

Lean:

```lean
import Mathlib

example : (1 : ℝ) + 2 = 3 := by norm_num

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
```

The Lean versions are useful, yet they require the user to know first: numerical equalities use `norm_num`, polynomials use `ring`; more complex cases still require remembering fact names in the library and citing them explicitly in source. Those names and call steps are not the mathematical facts themselves, yet they often consume large amounts of time and attention. Litex asks: once a user understands a fact, can they write it down directly and let the system do the tool work needed for checking—without first learning to memorize, search for, and name those grounds?

Next, the expression barrier. Our mathematical problem is that a function `f` accepts only positive reals, and we already know `x > 0`; we want to say that `f(x)` equals itself. A common Lean encoding is:

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

Lean uses a subtype to bind a value to a proof that it is positive, so a call must combine `x` and `hx` into `⟨x, hx⟩`. The design is precise and general, but the reader must cross that representation layer before seeing `f(x)`.

Litex still checks `x > 0`, but leaves it as an ordinary fact in the context, while the source still writes `f(x)`. What is omitted is hand-passing of evidence; the well-definedness checks for `f(x)` are done by the verifier for you.

> **Users write mathematics; the system searches for grounds.** What Litex saves is precisely the time and attention spent memorizing and calling fact names and tactic names: `1 + 2 = 3` need not be `by norm_num`, and a polynomial identity need not be `by ring`. When conditions suffice, the verifier helps find how each piece of mathematics is proved. That greatly lowers the barrier from “I understand” to “I can formalize.”

A problem facing AI for Math today is that AI may generate code that passes the Lean kernel while the actual proposition drops a hypothesis, changes a quantifier, or weakens a conclusion. The Lean kernel did not err; it correctly checked the proposition in the code. The error is that the formal statement did not align with the mathematical intent.

Ideally, Litex users attend to objects, conditions, facts, and conclusions, while Litex provides locally traceable feedback. *People who understand a domain but are not proof-assistant experts can still take part in formalization and know how far the system has checked.*

> **This is a design direction, not a claim that the current language, standard library, or compiler is already complete.**

</details>

<a id="summary-bottom-up-and-top-down"></a>

<details>
<summary><strong>Personal reflection: does Litex fill a paradigm gap in AI reasoning?</strong></summary>

In mathematical practice, bottom-up proof flow (starting from premises and accumulating more facts) and top-down proof flow (decomposing the final conclusion until it matches the premises) constitute different perspectives and approaches to mathematical proof. Litex source represents the former mode of thinking; Lean code represents the latter. Which mode does AI prefer?

Consider bottom-up proof flow first. Most mathematical textbooks are written in a bottom-up narrative pattern, which is also the thinking paradigm humans adapt to more readily (imagine: we do not start reading a mathematics book from the last page!). Large models are trained on mathematical knowledge from the internet, so AI finds Litex code easier to read. At the same time, when an AI agent writes Litex code and interacts with Litex's output—seeing why each stretch of proof is right and where it went wrong—it is easier to form a `human–AI–Litex` proof-flow construction.

Now consider top-down proof flow. Large-model training is organized around objective functions and reward signals. Thus AI need not naturally possess a stable ability to unfold reasoning from first principles bottom-up; in many tasks it more readily organizes, backward from a desired result or evaluation signal, a path that appears able to reach the result.

Therefore both modes of thinking are valuable: bottom-up suits accumulating reusable local facts and exposing intermediate grounds; top-down suits clarifying goals, choosing direction, and compressing the search space. Connecting Litex and Lean can place both directions in one checkable evidence chain and let humans and AI collaborate in the directions each is good at.

</details>

### For mathematicians

If you work in mathematics, what you may care about first is not yet another tool, but how mathematical understanding—and the traditional values mathematics represents—can be preserved in the AI era.

AI is bringing *reasoning abundance*: answers and proofs can be generated at scale, yet they are not automatically trustworthy or explainable, nor do they necessarily deepen understanding. As [Terence Tao said in his 2026 ICM public lecture](https://www.youtube.com/watch?v=M0--ZH1lOzg), the future of mathematics needs to shift toward verification, exposition, and digestion of proofs. More generally: how can AI-generated reasoning become shared knowledge that is checkable, understandable, and reusable—not only in mathematics, but across knowledge work?

Today’s mathematical world is not calm: hot topics rotate quickly, and AI sometimes makes mathematical problems chaseable like “mining.” In September 2026, Terence Tao and 25 Fields medalists warned that AI companies treating “fast problem-solving” as a measure of mathematical progress may sacrifice genuine understanding, originality, scholarly transmission, and norms of attribution, severely misaligning AI development goals with the mathematical community. [Original post](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/)

Litex does not oppose applications, nor deny that mathematics needs to land in practice; but we want people to recognize again that mathematics is first an activity of understanding. The value of mathematics lies in helping humans understand the world better.

What Litex aims to do is exactly to add a readable abstraction layer between formal verification and everyday mathematical thinking: so that you need not first become a proof-assistant expert to write down clearly “what I understand,” hand it to a machine to check, and then see the checking process and the mathematical structure behind it. What we seek is not a flashier tool, but a state in which anyone who has mathematics in mind can express it naturally in Litex and thereby deepen their grasp of the mathematics itself.

Part of that simplicity is categorical, not only notational. In ordinary mathematical writing, a number is not a theorem, and a theorem is not a type. Litex keeps that habit on the surface: objects, facts, and statements stay separate, so reading a file feels closer to reading mathematics than to learning a new encoding of mathematics. The claim is about expression and reading cost—not that every theorem becomes easier to prove.

Few communities understand better than mathematicians how essential a good symbol system is. From Arabic numerals to Leibniz’s notation, each renewal of symbols or writing format has greatly advanced mathematics itself; in modern times, LaTeX likewise made it easier for people to communicate with one another. What Litex wants to ask of that sensitivity is this: can the interface of a formal language also stay closer to the mental flow and habits mathematicians already use?

The history of science repeatedly shows that revisiting known problems from a fresh starting point often advances an existing field—and sometimes gives rise to a new one. Entering the AI era, complex problems keep appearing, and people increasingly need reasoning that is trustworthy, scalable, and explainable. Formal methods will play a larger role in that process. So another exploration like Litex is valuable in itself.

Historically influential theories often began from pure curiosity about the problem itself, not from calculation of short-term returns. The author of Litex hopes to push Math for AI from language—the lowest layer of the stack. Honestly, he did it because he was interested. May this blueprint spark an impulse to experience the beauty of mathematics through Litex.

<a id="reader-programmers"></a>

### For programmers

Litex’s design intent is in fact very simple: just as Fortran and C abstracted over parts of assembly language and made systems engineering and scientific computing easier, Python later abstracted over some uses of C and let people without a professional programming background take part. As programming languages became easier to learn and use, more people became programmers, and the computing industry expanded with them.

Programmers already know a related contrast: functional style leans toward *what* should hold; imperative style leans toward *how* to change state step by step. Here is the strange twist. Lean itself is a functional language, yet the everyday way of writing mathematics in Lean—tactic proofs—often reads as imperative *how*: each line attacks the current goal and rewrites the proof state. Litex flips that default back toward *what*: the source states the objects and facts that should hold; the verifier searches for *how*. The language underneath Lean is still functional; what feels inverted is the default *mathematical* authoring surface.

Here is a second twist, about typing *feel*. Classic functional languages such as Lisp are often dynamically typed, and that flexibility is part of what makes them convenient. Lean is also functional, yet when you use it to write mathematics—not ordinary programs—its type discipline is very strict, so the authoring surface feels closer to a static type system. Litex sits nearer the other pole: an object may belong to many sets when that is mathematically warranted, so the day-to-day interface feels more like Python—dynamic in spirit. This is an interface analogy, not a claim that Litex implements a dynamic type system in the programming-language sense.

If you already write code, another useful way to see Litex is as a language that keeps mathematical categories apart the way ordinary programs keep values, statements, and types apart. Lean’s default surface gathers objects, propositions, proofs, and types into one dependent term/type universe—powerful and uniform, but easy to read as “everything lives in one encoding.” Litex’s user surface separates objects, facts, and statements; a function remains an operation on objects, and a fact remains a claim that something holds. The verifier still checks well-definedness and grounds; what changes is what the source asks you to hold in working memory.

```text
Lean surface:  terms / types   (objects, propositions, proofs share one universe)
Litex surface: objects · facts · statements

Lean (as a language): functional / declarative
Lean tactic proofs:   often read as imperative how
Litex source:         declarative what; verifier finds how

Lean (writing math):  strict typing feel  ≈ static
Litex:                many-set membership ≈ dynamic (Python-like)
```

Roughly, Litex stands to Lean as C stands to assembly: Lean tactic proofs often name facts and call them explicitly; that is a burden on working memory—people usually remember proof *patterns* (shapes), not fact names. Assembly writes many memory addresses; C maintains a table from variable names to addresses. Litex is similar: it maintains a fact table and a rule table; you write directly what should be proved, and the kernel matches and replaces by the predicate name of each atomic fact as key (see Section 1)—without first memorizing scattered fact names. Lean cannot easily grow the same default mechanism, precisely because its language allows highly first-class quantification over propositions; [Section 1](#fact-oriented) discusses that boundary.

One can also look one layer deeper at the object interface: Litex’s user-visible layer is closer to set theory—the same object may belong to several sets; Lean’s default user layer emphasizes that each term lives under a definite type. Litex hopes to build a similar abstraction layer between mathematical reasoning and formal verification, so that users are not entangled in low-level implementation details and can keep attention on thinking itself.

There is a second experimental compilation route that programmers often care about: once a computational fragment is checked in Litex, Litex can try to emit runnable Python or C from it (Section 6.1)—again experimental, and narrow, not a full language backend.

### For readers in other knowledge domains

Beyond mathematics, Litex hopes to use simple syntax for objects, relations, conditions, and rules, together with clear verification feedback, to invite exploration of another way of expressing the relationship among human intuition, machine verification, and mathematical knowledge. Litex also hopes to explore entry points for formal languages in real knowledge work—from AI safety, explainability of AI outputs, financial risk control, and high-assurance software engineering to physics, chemistry, medicine, law, and engineering.

These are currently directions of exploration, not claims of existing support for those industries. Practitioners without a mathematical background are welcome to take part: use formal tools in their own fields to understand grounds, discover conflicts, and prevent errors.

<a id="overview-gallery"></a>

## Appendix: Source Gallery

These snippets are not a tutorial—only a look at what “write what you want to prove” looks like in Litex. The preceding chapters develop the design and its boundaries.

The simplest equality:

```litex
1 + 1 = 2
```

A polynomial identity:

```litex
forall a, b R:
    (a + b)^2 = a^2 + 2 * a * b + b^2
```

A set fact:

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

Nonnegative numbers stay nonnegative under addition:

```litex
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y
```

A well-defined call when the domain condition is already known:

```litex
forall f fn(t R: t > 0) R, x R:
    x > 0
    =>:
        f(x) = f(x)
```

A proposition—define once, then use as an atomic fact:

```litex
prop is_positive(x R):
    x > 0

forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)
```

A known `forall` fact used to prove a concrete atomic fact:

```litex
prop is_positive(n R):
    exist a R+ st {n > a}

claim:
    ? forall x R:
        x > 10
        =>:
            $is_positive(x)
    witness exist a R+ st {x > a} from 10

have a R:
    a > 10

$is_positive(a)
```

Existential quantifiers—witness first, then obtain from the `exist` fact:

```litex
witness exist x R st {x = 0} from 0

obtain zero from exist x R st {x = 0}
zero = 0
```

A theorem—name a reusable conclusion, then cite it (transitivity of divisibility):

```litex
prop divides_by(d, n Z):
    exist k Z st {n = d * k}

thm divides_transitive:
    ? forall a, b, c Z:
        $divides_by(a, b)
        $divides_by(b, c)
        =>:
            $divides_by(a, c)
    obtain k from $divides_by(a, b)
    obtain m from $divides_by(b, c)
    c = b * m = (a * k) * m = a * (k * m)
    witness $divides_by(a, c) from k * m:
        c = a * (k * m)

witness $divides_by(2, 6) from 3
witness $divides_by(6, 30) from 5

by thm divides_transitive(2, 6, 30) => $divides_by(2, 30)
```

A named function:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

A local `claim`—write the equalities that should hold along the way, without naming rewrite directions:

```litex
claim:
    ? forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    a * (b * g) = (a * b) * g = (c * d) * g = (c * d) * f = c * (d * f)
```

Proof by contradiction—show that “every real satisfies `x^2 >= x`” fails:

> **Migration example:** Current `src/` checking stops at `by_contra` (`by contradiction`). This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
by contra:
    ? not forall x R:
        x^2 >= x
    impossible 0.5^2 >= 0.5
```

Proof by cases—exhaust the split, then close the goal in each branch:

```litex
have fn k(x R) R by cases:
    case x = 2: 3
    case x != 2: 4

have x R

by cases:
    ? k(x) > 2
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2
```

Proof by induction—the sum of the first `n` odd positives is `n^2`:

> **Migration example:** Current `src/` checking stops at `internal_bug: name n is already bound in an enclosing parse scope`. This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
have fn kth_odd(k Z) Z = 2 * k - 1

thm sum_first_odds:
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) = n^2
    by induc n from 1:
        ? sum(1, n, kth_odd) = n^2

        ? from n = 1:
            kth_odd(1) = 2 * 1 - 1 = 1
            sum(1, 1, kth_odd) = kth_odd(1) = 1 = 1^2

        ? induc:
            kth_odd(n + 1) = 2 * (n + 1) - 1
            sum(1, n + 1, kth_odd) = sum(1, n, kth_odd) + kth_odd(n + 1) = n^2 + (2 * (n + 1) - 1) = (n + 1)^2
```

A `struct`—a group: operation, identity, inverse on a carrier, and uniqueness of the identity:

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

A `template`—a parameterized definition family, then `\name<args>` to materialize:

> **Migration example:** Current `src/` checking stops at `search_proof` (`p.first = 1`). This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
struct Triple<X set>:
    first X
    second X
    third X

template<X set>:
    have fn triple(a, b, c X) &Triple<X> = (a, b, c)

\triple<R>(1, 2, 3) = (1, 2, 3)

have p &Triple<R> = \triple<R>(1, 2, 3)
p.first = 1
```

A simple word problem—use ASCII identifiers in the current parser; comments may be written in Chinese:

```litex
# Mom's age is 3 times Xiao Ming's age plus 4; Xiao Ming is 15. How old is Mom?
have xiaoming_age R = 15
let mom_age = 3 * xiaoming_age + 4
mom_age = 3 * 15 + 4 = 49
```

You supply the mathematical move; Litex checks each connection and keeps what passed.

Exact decimal construction normalizes aliases such as `2.400` and `2.4` before
comparison and persistence. The imaginary unit has a dedicated nonzero builtin,
and complex division retains denominator evidence. Finite sums and products
share an evaluator with the equality verifier: checked function application,
binding-aware substitution, recursive exact evaluation, then accumulation.
Each evaluation shares a 1024-term allowance across nested aggregates and
checks integer endpoint overflow. Separate symbolic rules retain their domain,
pointwise or partition premises. Detailed results expose the term calculations;
`eval` displays a value without publishing a fact. The
[aggregate tracer](../examples/proof_nodes/equal/by_builtin_rule/aggregate_calculation.lit)
and [symbolic tracer](../examples/proof_nodes/equal/by_builtin_rule/aggregate_identities.lit)
exercise these paths. These verifier paths do not establish Lean export support.
