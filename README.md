<div align="center">
  <img src="./assets/logo.PNG" alt="Litex logo" width="300">

# Litex

### The High-Level Language for Formal Mathematics
*(The Python of Formal Reasoning)*

Created and maintained by Jiachen Shen.

[Website & Playground](https://litexlang.com/) · [Blueprint](docs/Litex_Blueprint.md) · [Learn Litex](docs/Manual.md) · [Setup](docs/setup.md) · [Zulip Community](https://litex.zulipchat.com/) · [中文说明](docs/中文README.md)
</div>

---

## What is Litex?

**Litex is a high-level programming language for formal mathematics.**

In computer science, software engineering evolved from raw machine code (0101) to assembly instructions, and ultimately to high-level languages like C and Python. High-level languages abstracted away registers, stack frames, and manual memory addresses, freeing engineers to express complex ideas at the problem level.

Formal mathematics is going through the exact same evolution today:

```text
┌────────────────────────────────────────────────────────────────────────┐
│                               Litex                                    │
│             High-Level Language for Formal Mathematics                 │
│    • Math-centric declarations      • Automatic well-definedness check │
│    • Bounded routine auto-inference  • AI-agent native REPL session    │
└───────────────────────────────────┬────────────────────────────────────┘
                                    │ Compiles & Replays proofs
              ┌─────────────────────┼─────────────────────┐
              ▼                     ▼                     ▼
       ┌──────────────┐      ┌──────────────┐      ┌──────────────┐
       │    Lean 4    │      │  Coq / Rocq  │      │   Isabelle   │
       │    Kernel    │      │    Kernel    │      │    Kernel    │
       └──────────────┘      └──────────────┘      └──────────────┘
              ▲                     ▲                     ▲
              └─────────────────────┴─────────────────────┘
                     Low-Level Formal Verification Engines
```

Today, interactive theorem proving is still largely in its "assembly language" era. In traditional proof assistants (such as Lean, Coq, and Isabelle), users spend most of their cognitive energy managing low-level proof plumbing: navigating hidden goal stacks with `goto`-like tactic scripts (`intro`, `apply`, `simp`), threading hypothesis labels, and wrestling with dependent type coercion.

**Litex brings the high-level language paradigm to formal mathematics:**
1. **Math-Centric**: You declare definitions, state facts, and write the essential steps of a mathematical proof directly in clean, Pythonic syntax.
2. **Automates the Routine**: The compiler automatically verifies expression well-definedness, checks domain constraints, and searches contextual facts to validate intermediate steps.
3. **Universal High-Level Frontend**: Litex does not replace formal verification engines—it elevates them. Verified Litex proofs can be compiled down to **Lean 4**, **Coq**, or **Isabelle** for independent, ironclad kernel verification.

---

## Core Pillars

### 1. Syntax: Math as Code (Think in Mathematics, Not Tactics)

Litex syntax looks and reads like textbook mathematics. Instead of imperative tactic scripts that mutate a hidden proof state, Litex separates mathematical objects, facts, and structured deductive steps so static text matches natural mathematical writing:

```litex
forall x R:
    x^2 >= 0
```

The mathematical sentence supplies its own structure: `forall` introduces universal quantification, `R` specifies the real carrier, and `x^2 >= 0` is the checked conclusion.

Because Litex eliminates type-coercion wrappers across number sets ($\mathbb{N}^+ \subset \mathbb{Z} \subset \mathbb{Q} \subset \mathbb{R}$) and hypothesis-handle boilerplate, every clause in an ordinary mathematical sentence maps directly to Litex with a **[de Bruijn factor](examples/litex_vs_lean_speed/README.md#de-bruijn-factor) ($\text{formal length} \div \text{informal length}$) near 1**:

<table>
<tr>
<th width="34%">Natural Mathematical Writing</th>
<th width="30%">Litex (DF* ↓)</th>
<th width="36%">Lean 4 (DF* ↓)</th>
</tr>
<tr>
<td>

For every integer $a$ and positive natural number $d$, $a = d \lfloor a/d \rfloor + (a \bmod d)$.

</td>
<td>

```litex
# DF* = 0.35 (71.4% shorter)
forall a Z, d N+:
    a = d * quot(a, d) + a % d
```

</td>
<td>

```lean
-- DF* = 1.24
example : ∀ (a : Int) (d : Nat), 0 < d →
    a = (d : Int) * (a / (d : Int)) + a % (d : Int) :=
  fun a d _ =>
    (Int.mul_ediv_add_emod a (d : Int)).symm
```

</td>
</tr>
<tr>
<td>

The finite set $\{1, 2, 3\}$ has three elements.

</td>
<td>

```litex
# DF* = 0.44 (40.9% shorter)
finite_set_size({1, 2, 3}) = 3
```

</td>
<td>

```lean
-- DF* = 0.75
example : ({1, 2, 3} : Finset Nat).card = 3 :=
  by decide
```

</td>
</tr>
</table>

### 2. Semantics: Authentic Mathematical Domains

A signature feature of Litex's language semantics is how it handles **mathematical domains**.

In traditional type-theoretic provers, every function on a type must be total: partial operations (like $1/x$, $\sqrt{x}$, or $\ln(x)$) either adopt artificial out-of-domain defaults (such as $1/0 = 0$) or require verbose dependent subtype proofs bundled at every call site. In Litex, domain conditions are a first-class part of function semantics, and the language **automatically verifies domain obligations at the point of use**:

```litex
# Define a reciprocal function guarded by x != 0
have fn reciprocal(x R: x != 0) R = 1 / x

# Calling it with a valid input succeeds automatically:
reciprocal(2) = 1 / 2
```

If an author (or an AI agent) calls `reciprocal(0)`, Litex rejects it immediately at the well-definedness stage with a clear, structural diagnosis:

```text
WellDefinedError: object reciprocal(0) is not well-defined
  --> failed to verify function domain fact: 0 != 0
```

You focus on the mathematical argument; the language automatically ensures that every expression remains mathematically valid.

### 3. How Litex Works: Relational Search Instead of $\lambda$-Calculus Elaboration

Litex was designed around a simple engineering goal: **over 500,000 lines of pure Rust, written for a language that is effortless to write and a checker that is blazingly fast.**

Why can Litex be designed this way? Whether you write in everyday mathematics, Lean, Coq, or Isabelle, each system encodes mathematical objects differently under the hood—yet **the core mathematical conclusions and relational laws (such as $1 + 1 = 2$, order transitivity, and algebraic identities) are universal consensus.**

Traditional provers verify a statement by elaborating surface tactics and typeclasses into explicit dependent $\lambda$-calculus proof terms (see [how `1 + 1 = 2` is elaborated in Lean](examples/litex_vs_lean_speed/lean-proof-pipeline.md)). Litex works on a fundamentally different principle—**bounded relational search** directly over this shared mathematical consensus:
1. **Retrieve**: Searches the active scope's relational indices for cited definitions, established facts, and builtin mathematical rules without manual hypothesis labels.
2. **Verify**: Normalizes algebraic expressions, checks domain obligations, matches variable binders, and validates premises.
3. **Commit**: Records a traceable JSON proof record and makes the accepted conclusion available to all subsequent steps.

Authors supply the mathematical creativity—key intermediate lemmas, witnesses, case splits, and induction arguments. Litex takes care of the routine algebraic and logical bridges.

<a id="readme-comparisons"></a>
<a id="expression-length-and-checking-speed"></a>

Because Litex relies on bounded relational search and dedicated Rust normalization rather than dynamic tactic elaboration and $\lambda$-term construction, ordinary mathematical steps verify in sub-millisecond time:

| Mathematical task | Litex (ms) ↓ | Lean (ms) ↓ | Lean ÷ Litex |
| --- | ---: | ---: | ---: |
| [The set of positive reals is nonempty](#readme-example-witness_nonempty_positive) | 0.084 | 6.439 | **76.9×** |
| [Natural-number arithmetic: 1 + 1 = 2](#readme-example-nat_mathlib) | 0.037 | 1.361 | **36.7×** |
| [The sum of two positive reals is positive](#readme-example-forall_add_pos) | 0.392 | 10.487 | **26.7×** |
| [The derivative of the square function at 3 is 6](#readme-example-derivative_square_at_three) | 1.464 | 29.945 | **20.5×** |

*(Historical local benchmarks using warm medians excluding startup and imports. See the [full benchmark report](examples/litex_vs_lean_speed/README.md) for detailed methodology and comparisons.)*

### 4. Built for AI Mathematicians (Agent-Native Architecture)

Because Litex's relational search is bounded and traversable, its verification output is natively suited for AI mathematical reasoning:

* **Pythonic Syntax**: Natural for Large Language Models to read and generate without getting trapped in complex tactic grammars.
* **Persistent Session (`litex -session`)**: Unlike traditional batch provers that reset on failure, Litex provides a stateful REPL. When a candidate step is rejected, **previously accepted context remains intact**. An agent can propose a statement, inspect the feedback, repair the single failed line, and proceed.
* **Traceable JSON Diagnostics**: When a step succeeds, Litex's JSON record traces how it was derived; when a step fails (such as forgetting a domain condition like $x \neq 0$), it pinpoints the exact missing mathematical premise so the agent can self-correct on the next turn.

```bash
litex -strict -session -e 'have a R = 2'
litex> a = 3
# {"run_result": "failure", "session_terminated": false}
litex> a + 1 = 3
# {"run_result": "success", "session_terminated": false}
```

### 5. One High-Level Source, Multi-Target Ecosystem

That same traceable JSON proof record also acts as a dual-purpose intermediate representation (Evidence IR): because Litex's rules rest on universal mathematical consensus, backend compilers can replay the recorded proof steps into target systems without secondary proof search:

* **Compiler Bridge to Formal Kernels**: Compile checkable Litex proofs to standalone Lean 4 files (`litex -lean -f proof.lit`) for independent verification by Lean's kernel. The compiler architecture is designed to expand to Coq/Rocq and Isabelle.
* **Publication-Ready LaTeX**: Export proofs directly into beautifully typeset LaTeX lecture notes, handouts, or papers (`litex -latex -document -f proof.lit`).
* **Interactive Textbooks & Knowledge Graphs**: Interactively browse definitions, premises, and dependency graphs with `litex -reading`.
* **Executable Code Extraction**: Extract computational mathematical definitions directly into Python and C (`litex -extractpython`, `litex -extractc`).

---

## Quickstart

### Installation

**macOS / Linux (Homebrew):**
```bash
brew install litexlang/tap/litex
```

**Windows (Scoop):**
```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
```

**Online Playground:** Try Litex instantly in your browser at [litexlang.com](https://litexlang.com/).

### First Commands

```bash
# Verify a single mathematical statement
litex -e '1 + 1 = 2'

# Start an interactive mathematical session
litex -session

# Check a proof file
litex -f proof.lit

# Compile a proof to Lean 4
litex -lean -f proof.lit

# Generate a complete LaTeX document
litex -latex -document -lang en -f proof.lit
```

---

<a id="litex-reliability"></a>

## Project Status & About

Litex is an independent research project started in 2024, created and actively maintained by **Jiachen Shen (沈嘉辰)**, a mathematics PhD student at Fudan University.

The project is currently in **Beta**. We are actively expanding language features, standard library theorems, and compiler backends. If you encounter an issue or have a feature suggestion, please include a minimal reproducible example when opening an issue.

* **Website**: [litexlang.com](https://litexlang.com/)
* **Community**: [Zulip](https://litex.zulipchat.com/)
* **GitHub Issues**: [github.com/litexlang/golitex/issues](https://github.com/litexlang/golitex/issues)
* **Email**: litexlang@outlook.com

Special thanks to Wei Lin, Siqi Sun, Peng Sun, Chenxuan Huang, Yan Lu, Sheng Xu, Hao Wu, Keyao Zhu, Zhaoxuan Hong, and Qiushi Geng for their support and advice.

Released under the [Apache License 2.0](LICENSE).

---

## Appendix: Complete Side-by-Side Examples

Each example runs independently. Expand a title for the complete Litex and Lean code.

<details id="readme-example-nat_mathlib">
<summary>1. Natural-number arithmetic: 1 + 1 = 2</summary>

**Litex**

```litex
1 + 1 = 2
```

**Lean**

```lean
import Mathlib

example : (1 : Nat) + 1 = 2 := by rfl
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-positive_nonzero">
<summary>2. Every positive real number is nonzero</summary>

**Litex**

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

**Lean**

```lean
import Mathlib

example (x : ℝ) (hx : x > 0) : x ≠ 0 := by
  exact ne_of_gt hx
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-square_witness">
<summary>3. A real number whose square is 4: choose 2 as a witness</summary>

**Litex**

```litex
witness exist w R st {w^2 = 4} from 2
```

**Lean**

```lean
import Mathlib

example : ∃ w : ℝ, w ^ 2 = 4 := by
  refine ⟨2, ?_⟩
  norm_num
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-guarded_reciprocal">
<summary>4. Define and call a reciprocal function on nonzero reals</summary>

**Litex**

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

**Lean**

```lean
import Mathlib

noncomputable def reciprocal (x : {y : ℝ // y ≠ 0}) : ℝ :=
  (x : ℝ)⁻¹

example : reciprocal ⟨2, by norm_num⟩ = (2 : ℝ)⁻¹ := by
  simp [reciprocal]
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-log_2_8">
<summary>5. Logarithms: log₂8 = 3</summary>

**Litex**

```litex
log(2,8)=3
```

**Lean**

```lean
import Mathlib

example : Real.logb 2 8=3 := by
  rw [show (8:Real)=2^3 by norm_num, Real.logb_pow]
  rw [Real.logb_self_eq_one (by norm_num : (1:Real)<2)]
  norm_num
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-prime_1000000007">
<summary>6. Number theory: 1000000007 is prime</summary>

**Litex**

```litex
$prime(1000000007)
```

**Lean**

```lean
import Mathlib

example : Nat.Prime 1000000007 := by native_decide
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-witness_nonempty_positive">
<summary>7. Set theory: the set of positive reals is nonempty</summary>

**Litex**

```litex
witness $is_nonempty_set({x R:x>0}) from 1
```

**Lean**

```lean
import Mathlib

example : Set.Nonempty {x : Real | 0 < x} := ⟨(1 : Real), (show (0 : Real) < 1 from zero_lt_one)⟩
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-named_theorem">
<summary>8. Define and apply the theorem that positive reals are nonzero</summary>

**Litex**

```litex
thm bench_positive_is_nonzero:
    ? forall x R:
        x>0
        =>:
            x!=0
release thm bench_positive_is_nonzero(3)
```

**Lean**

```lean
import Mathlib

theorem bench_positive_is_nonzero : ∀ x : Real, 0 < x → x ≠ 0 := by
  intro x hx
  exact ne_of_gt hx
theorem bench_use : (3 : Real) ≠ 0 := bench_positive_is_nonzero 3 (by norm_num)
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-predicate">
<summary>9. Define an open-interval predicate and check membership</summary>

**Litex**

```litex
prop bench_in_open(x,a,b R):
    a<x
    x<b
by def $bench_in_open(1,0,2)
```

**Lean**

```lean
import Mathlib

def bench_in_open (x a b : Real) : Prop := a < x ∧ x < b
theorem bench_use : bench_in_open 1 0 2 := by norm_num [bench_in_open]
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-forall_add_pos">
<summary>10. Universal statement: the sum of two positive reals is positive</summary>

**Litex**

```litex
forall x,y R:
    x > 0
    y > 0
    =>:
        x+y > 0
```

**Lean**

```lean
import Mathlib

theorem bench : ∀ x y : Real, 0 < x → 0 < y → 0 < x+y := fun x y hx hy => add_pos hx hy
```

[Back to comparisons](#readme-comparisons)

</details>

<details id="readme-example-derivative_square_at_three">
<summary>11. The derivative of the square function at 3 is 6</summary>

**Litex**

```litex
$has_derivative_at(fn(t R) R {t^2},3,6)
```

**Lean**

```lean
import Mathlib

theorem bench : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by have h := hasDerivAt_pow 2 (3 : Real); norm_num at h; exact h
```

[Back to comparisons](#readme-comparisons)

</details>
