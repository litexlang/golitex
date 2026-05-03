# Mechanics of Litex

Try all snippets in browser: https://litexlang.com/doc/Mechanics_of_Litex

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Mechanics_of_Litex.md


This note is a **single map** of how Litex works for readers who already think in terms of **math as facts**. It is **not** a complete syntax reference or a full catalog of builtins. Other write-ups cover the builtin overview, statement inventory, verification rules, inference rules, and a short tutorial in the same docs tree.

**Suggested reading order (narrative spine):**

1. **Vocabulary layer** — built-in objects and facts; why combinatorics explode.  
2. **User extension layer** — `prop` and `forall` for new notions and links.  
3. **Reasoning layer** — facts implying facts (exact match, specialization, matching/substitution).  
4. **Verification pipeline** — well-definedness, verification goals, `forall`, then **inference** after facts are stored (verification closes goals during checking; inference enriches context afterward).  
5. **Contrast** — math vs everyday programming.  
6. **Bridge** — where Litex still borrows programming-shaped tools.  
7. **Statements** — what you write at the top level (detailed lists live in the statement reference).  
8. **Traceability** — how a checked line points to **cited facts** or **builtin rules**.  
9. **Appendices** — taxonomy of builtin *kinds*, then **self-contained litex fragments** illustrating common patterns.

---

## 1. Built-in vocabulary and combinatorics

Litex ships a **base layer**: families of mathematical objects, core facts packaged as **verification** behavior, special builtin `prop`-like predicates, a small stock of **logical surface forms** (`or`, `not`, `forall`, …), and a menu of **statement** forms (`prove`, `know`, `have`, `by …`, …). The **counts** (how many object kinds, how many packaged facts, …) are **order-of-magnitude** targets, not a promise you should memorize; they can change as the language grows.

Each piece alone is usually **small** and each link between two builtin pieces is often **obvious in isolation**. What grows quickly is **composition**: every object shape interacts with many fact shapes, and small local rules add up to a large builtin graph.

Those links are **authored into the system**. Many links do **not** require research-level math: a typical undergraduate math major can judge whether a rule is right, and a typical CS major can encode it. **Automation** (tools or capable assistants) is a good fit for generating and maintaining this **bulk** work responsibly.

**Design stance:** which objects are **“basic”** is a **language design** choice. How strong builtins feel—how often you get “for free” without a user `prop`—depends on how **complete** that builtin graph is, not on a single magic switch.

---

## 2. `prop` and `forall`: the user extension layer

Beyond the builtin vocabulary, mathematics in Litex is open-ended: you define **new** predicates and relate **new** facts to old ones.

- **`prop`** introduces a **user-defined predicate** (a new “property” name with parameters and a defining body, optionally with `iff`/`=>:` / `<=>:` structure as the language allows). The system does **not** ship a second, separate builtin graph **between** your new predicate and every other concept except what **verification** can already see through definitions and facts you prove.
- **`forall`** states **universal** links: under hypotheses (parameters and assumptions), certain conclusions hold.

**Glossary:** **`prop`** ≈ definitional or axiomatic predicate you name; **`forall`** ≈ “for all …, if … then …” at the surface of a fact.

Minimal schematic (definition only; verification of uses is separate):

```litex
prove:
    prop unit_x(x R):
        forall x R:
            =>:
                x = 1
            <=>:
                x + 0 = 1
```

Once `unit_x` exists, **`$unit_x(t)`** is an **atomic** fact; **post-storage inference** may then add parameter-typing facts and **instantiated** pieces of the definition body for the actual arguments `t`.

---

## 3. Establishing links: facts implying facts

In essence, **mathematics here is facts implying facts.** Builtin **verification** steps are **finite**, but **user-defined** concepts can **multiply without bound** (informally: definitions breed lemmas; lemmas breed more statements). So users must be able to **derive** new facts from what is already in context.

Two recurring mechanisms:

1. **Exact-match reuse** — a goal or a new line matches a **known fact** already in the environment (same shape after routine processing). Equality goals also benefit from **normalization** and **transitivity-style** reasoning baked into verification.
2. **`forall` specialization** — a universal fact **instantiates** to particular terms when parameters and hypotheses match; the conclusion becomes available for those terms.

**Optional third bucket (mental model):** **`know`** and **definition unfolding** change the context *before* you close a goal: they are not a separate “logic,” but they alter which facts **exact matches** and **`forall`** steps can see.

---

## 4. Matching and substitution (cross-cutting)

**Matching** asks whether a **pattern** (a fact or goal with parameters and structure) fits a **concrete** piece of mathematics in context. **Substitution** plugs chosen terms into the pattern’s holes once a match succeeds.

This pair is not private to **`forall`**. The same idea appears when:

- Connecting an **equality** or **predicate** fact to a goal;
- Using **`by` tactics** (`by cases`, `by contra`, induction-style blocks, …) that introduce subsidiary goals whose shape echoes the main goal;
- Relating **atomic** facts (`$P(args)`) to **definitions** of `P`.

This document stays **implementation-agnostic**: it describes what users rely on, not internal data structures.

---

## 5. End-to-end proof flow (verify vs infer)

When the checker works on a **proof obligation**, a useful mental checklist is:

1. **Well-definedness** — names, types, and defining bodies are coherent (e.g. `prop`, `have`, `fn` headers).
2. **Builtin verification** — goals closed by **builtin verification rules**: arithmetic, comparisons, set membership gadgets, logical maneuvers the language chose to automate.
3. **Known facts** — **exact** (or equality-aware) reuse of facts already established in the proof or introduced with **`know`**.
4. **`forall`** — instantiate universal theorems or lemmas to the instance at hand.
5. **Tactics** — `by cases`, `by contra`, induction, enumeration, … .

**After** a fact is **accepted** and **stored**, **inference** may add further **facts** or bookkeeping used later. That pass is **not** the same thing as **closing a goal during verification**: inference **enriches context** once the checker agrees the fact is legitimate; verification **discharges obligations** while checking.

**Failure modes (user-facing):** a goal may remain **unproved** (retry with more lemmas or structure), or checking may stop with **error** (ill-formed input or an impossible obligation). The implementation’s internal labels need not concern readers of this overview.

---

## 6. Litex vs ordinary programming

Litex is **not** “a programming language with funny syntax.” **Meaning** is driven by **proof obligations and facts**, not by a global notion of **executing** a program to obtain a usable value at every step.

- **Functions as nouns** — in classical math notation, a function is usually a **term** (an object in a function space). In imperative programming, `f(x)` is an **action** producing a value. Litex leans toward the **math** reading: `fn` types and laws live next to equalities and memberships.
- **Truth, not arbitrary dataflow** — a prior line in a proof contributes **truth** in context (`false` / `true` / “still open” / **error** on ill-formed input), not a generic **typed value** piped into the next statement the way `x = f(); y = g(x)` works in C-like languages.
- **Existence** — introducing a novel object often requires **proving** it exists (or assuming it under `forall` / `exist` patterns). Programming often **allocates** or **reads** without that exercise.
- **No class inheritance** — mainstream math does not say “this vector **extends** that widget.” A single value can lie in **many** sets (`R`, `C`, a subspace, …). Type systems optimized for single-inheritance chains are a poor mental model for that flexibility.
- **No general control flow** — there is no `while`/`goto` proof semantics. Structured **`by`** blocks and **`algo`** are specialized devices, not arbitrary control graphs.

**Sidebar — misleading analogy:** “A Litex file is like a script that runs top to bottom and passes values.” **Correction:** it is like a **document of claims** checked under explicit rules; only **`eval`** / certain **`algo`** paths behave like traditional evaluation, and even then they sit beside proof obligations.

---

## 7. Where programming habits still help

Litex deliberately imports a few **program-shaped** constructs because they match mathematical practice.

**Anonymous functions** — lambdas as terms in function spaces (syntactic kin to functional programming; **role** is proof-centric, not “call for side effects”):

```litex
prove:
    have f fn(x R) R = 'R(x){x}

    f(1) = 'R(x){x}(1) = 1
```

**`algo`** — a named recipe attached to a function, used with **`eval`** when you want calculator-style follow-through:

```litex
prove:
    have fn f(x R) R = 1

    algo f(x):
        1
```

```litex
prove:
    have f fn(x, y R) R

    know:
        forall x, y R:
            f(x, y) = f(x - 1, y) + 1

        forall x, y R:
            x = 0
            =>:
                f(x, y) = y

    algo f(x, y):
        case x = 0: y
        f(x - 1, y) + 1

    eval f(10, 20)

    f(10, 20) = 30
```

**`have fn` with case splits** — introduce a function piecewise, generating the corresponding `forall` clauses:

```litex
have fn self_max(x, y R) R:
    case x > y: x
    case x <= y: y
```

**What they are not:** a replacement for **`forall`** theorem proving, or a license to skip **well-definedness** and verification when the story is actually mathematical.

---

## 8. Statements (surface syntax)

At file level, Litex is built from **statements**: definitions (`prop`, `struct`, `family`, …), declarations (`have`, `let`), proof blocks (`prove`, `claim`), imports, and more. The dedicated **statement reference** spells out names and shapes; the **introduction tutorial** motivates them. **Mechanics** does not duplicate that grammar here.

---

## 9. Traceability: cited facts and builtin rules

So users can **audit** a check, the system can report **how** a line was justified:

- **`known_fact` / cited fact** — the step overlaps an explicit fact already in the context (possibly after matching or equality reasoning).
- **Builtin rule** — the step is accepted by a **named builtin verification rule** from the checker’s library, rather than by a user lemma you stated separately.

You will **not** see a full **formal proof object** for microscopic logic (e.g. a complete Hilbert-style derivation of `1 + 1 = 2`) in the style of some other proof assistants. Litex **trusts** its finite builtin layer for those steps and exposes **rule names** or **matches** instead of deep proof terms. That matches the appendix distinction between **core verification rules** and **user-visible traces**.

---

## Appendix A — Taxonomy of builtin *kinds*

This appendix classifies **what the language ships**, not every concrete rule name.

### A.0 Three layers (orthonormal to “objects vs logic”)

1. **Base definitions** — how builtin sorts (`N`, `R`, `fn(…)`, `cart(…)`, …) are introduced and related to **sets** and typing discipline.
2. **Convenience verification rules** — shortcuts that make common textbook steps fast (heavy in **comparison** and arithmetic normal forms). Without them proofs would be longer; they are still **checker-chosen**, not user `prop`s.
3. **Core verification rules** — the minimal **non-negotiable** gadgetry that replaces handwriting endless syllogisms and tiny arithmetic goals. See the contrast with Lean/Metamath in §A.3.

### A.1 Set-theoretic stance and standard objects

- **Everything is modeled as a set** in a broad, language-appropriate sense; **typed** sets (`N`, `R_pos`, …) are still **sets** with extra literature-compatible facts.
- **Finite sets and enumeration** — finiteness, counting, and “member of a small explicit set ⇒ disjunction of equalities” (see Appendix B).
- **`range` / `closed_range`** — integer intervals and bound reasoning (see Appendix B).
- **Products and functions** — tuples and Cartesian products as sets; **`fn`**, **struct**, **family** tie into the same picture (see Appendix B).
- **Proof maneuvers ↔ logic** — `by cases` aligns with **`or`**; `by contra` aligns with **`not`** (see Appendix B).

### A.2 Operators and relations

- **Arithmetic** — `+ - * / %`, `abs`, `max`, `min`, `sum`, `product`, and standard algebraic/order lemmas.
- **Relations** — strict and weak orders, compatibility with **`or`**, and similar low-level facts (see Appendix B).

### A.3 “Baked in” vs “fully explicit” proof assistants

Steps such as routine **syllogistic** patterns or small **numeric** goals (e.g. `1 + 1 = 2`) are **intended** to be **accepted by builtin rules**, not written as user `prop` lemmas. That differs from:

- **Lean** — where low-level logic is often **explicit** in the tactic or term language; and  
- **Metamath** — where even `1+1=2` is a **long** derivation from a tiny logic.

Litex also **does not surface** machine-grade **proof terms** for every micro-step; users see **which rule or fact** carried the step instead.

### A.4 Small set-theoretic illustration

Positive naturals are never below 1:

```litex
forall a N_pos:
    1 <= a
```

---

## Appendix B — Illustrative litex fragments

Each block is **self-contained** (it is what the test runner executes from this file). They are **not** a minimal course; they show shapes that often appear in real scripts.

### B.1 Finiteness and counting

```litex
$is_finite_set({1, 2})
count({1, 2, 3}) = 3
```

### B.2 Membership in a finite enumeration

```litex
forall a R:
    a $in {1, 2}
    =>:
        a = 1 or a = 2
```

### B.3 Integer half-open interval

```litex
forall i Z:
    i $in range(2, 6)
    =>:
        2 <= i
        i < 6
```

### B.4 Tuple and Cartesian product as sets

```litex
let a set:
    a = (2, 3)

$is_tuple(a)
```

```litex
let b set:
    b = cart(R, Q)

$is_cart(b)
```

### B.5 Plain sethood of a literal set

```litex
prove:
    $is_set({1, 2})
```

### B.6 Proof by cases (disjunction-flavored)

```litex
prove:
    by cases:
        prove:
            1 + 1 = 2
        case 1 + 1 = 2:
            do_nothing
        case 1 + 1 != 2:
            1 + 1 = 2
            impossible 1 + 1 = 2
```

### B.7 Proof by contradiction (interface shape)

```litex
by contra => 1 = 1:
    impossible 1 != 1
```

### B.8 Disjunction from order facts

```litex
prove:
    2 <= 3 or 3 < 2
```

### B.9 Two linear equations in two unknowns

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = (10 - 3 * 6) / 2 = -4
```

### B.10 A primality predicate (definition only)

```litex
prove:
    prop prime(a N_pos):
        2 <= a
        forall b N_pos:
            2 <= b < a
            =>:
                a % b != 0
```
