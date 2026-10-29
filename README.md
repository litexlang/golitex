<div align="center">
  <img src="./assets/logo.PNG" alt="Litex logo" width="300">

# Litex

### The Python of Formal Language

**Pronunciation:** /ˈliːtɛk/ (“LEE-tek”, Chinese “里泰克”).

Created and maintained by Jiachen Shen. The main text is author-written, with AI assistance for clarity.

[Website and playground](https://litexlang.com) · [GitHub](https://github.com/litexlang/golitex)
</div>

Mathematical writing already carries logical structure: statements, assumptions and definitions provide much of the reasoning needed to justify each step. Litex is a formal language designed to make this structure executable through proof search over contextual facts and built-in mathematical rules.

Authors supply meaningful mathematical steps, while the system recovers the supported inferences connecting them. Humans and AI can work in terms of mathematical facts without having to spell out every formal derivation.

Selected local comparisons show compact mathematical expression and, on some examples, 10–100× faster native checking than Lean, excluding startup and imports. Its verification records support interactive reading, writing and correction, with promising initial AI-agent results. It also compiles supported proofs to Lean for independent rechecking.

<a id="readme-comparisons"></a>

## Familiar expressions, familiar mathematics

The same mathematics, written in Litex and Lean. Click an example for its complete code in the appendix.

| Mathematical expression | Litex | Lean (with `import Mathlib`) |
| --- | --- | --- |
| [Natural-number arithmetic: 1 + 1 = 2](#readme-example-nat_mathlib) | `1 + 1 = 2` | `example : (1 : Nat) + 1 = 2 := by rfl` |
| [Every positive real number is nonzero](#readme-example-positive_nonzero) | `forall x R: x > 0 => x != 0` | `example (x : ℝ) (hx : x > 0) : x ≠ 0 := by` |
|  |  | `  exact ne_of_gt hx` |
| [A real number whose square is 4: choose 2 as a witness](#readme-example-square_witness) | `witness exist w R st {w^2 = 4} from 2` | `example : ∃ w : ℝ, w ^ 2 = 4 := by` |
|  |  | `  refine ⟨2, ?_⟩` |
|  |  | `  norm_num` |
| [Define and call a reciprocal function on nonzero reals](#readme-example-guarded_reciprocal) | `have fn reciprocal(x R: x != 0) R = 1 / x` | `noncomputable def reciprocal (x : {y : ℝ // y ≠ 0}) : ℝ :=` |
|  | `reciprocal(2) = 1 / 2` | `  (x : ℝ)⁻¹` |
|  |  |  |
|  |  | `example : reciprocal ⟨2, by norm_num⟩ = (2 : ℝ)⁻¹ := by` |
|  |  | `  simp [reciprocal]` |

<a id="expression-length-and-checking-speed"></a>

### Checking time on selected examples

These historical local measurements select cases where Litex's native checking path was faster. Times exclude startup, dependency imports and Litex-to-Lean rechecking; ratios use unrounded median times. See the [measurement method](examples/litex_vs_lean_speed/README.md) and [unscreened comparison](examples/litex_vs_lean_speed/search-and-expansion.md), where Lean's direct route was faster in five of six cases.

| Mathematical task | Litex (ms) ↓ | Lean (ms) ↓ | Lean ÷ Litex |
| --- | ---: | ---: | ---: |
| [Logarithms: log₂8 = 3](#readme-example-log_2_8) | 0.064 | 13.992 | **217.0×** |
| [Number theory: 1000000007 is prime](#readme-example-prime_1000000007) | 0.027 | 4.029 | **147.2×** |
| [Set theory: the set of positive reals is nonempty](#readme-example-witness_nonempty_positive) | 0.084 | 6.439 | **76.9×** |
| [Define and apply the theorem that positive reals are nonzero](#readme-example-named_theorem) | 0.158 | 8.018 | **50.7×** |
| [Define an open-interval predicate and check membership](#readme-example-predicate) | 0.189 | 8.223 | **43.4×** |
| [Natural-number arithmetic: 1 + 1 = 2](#readme-example-nat_mathlib) | 0.037 | 1.361 | **36.7×** |
| [Universal statement: the sum of two positive reals is positive](#readme-example-forall_add_pos) | 0.392 | 10.487 | **26.7×** |
| [The derivative of the square function at 3 is 6](#readme-example-derivative_square_at_three) | 1.464 | 29.945 | **20.5×** |

Expression length is reported separately as [retrospective normalized-character ratios (DF*)](examples/litex_vs_lean_speed/README.md#de-bruijn-factor), using shared informal texts written after the formal sources. Those examples do not establish a general de Bruijn factor or measure ease of reading or writing.

## Why I built Litex

**Could mathematics itself be the formal language?** Mathematical writing already introduces objects, gives definitions, states assumptions and justifies conclusions. I want to preserve that correspondence while adding enough structure for mechanical checking.

Doing mathematics means looking for patterns. In Litex, I have been looking for recurring patterns in the act of proving: how statements introduce conditions, how facts connect, and how a conclusion finds support in its context. My aim is to turn those patterns into executable mechanisms, so humans and AI can concentrate on the mathematics.

My ambition is for Litex to become a Python for formal mathematics: familiar writing, few language conventions, and useful machinery behind each statement. As AI produces more candidate reasoning, the language in which we understand, check and share mathematical knowledge matters more.

### Mathematical wording becomes a checking action

Litex starts with usable mathematical objects and their conditions: numbers, sets and functions can be named directly. Familiar proof phrases then correspond to precise statements. The source column below contains excerpts; the [Manual](docs/Manual.md#mathematical-reading) gives complete forms and scope rules.

| Mathematical wording | Litex excerpt | What connects the step to its grounds |
| --- | --- | --- |
| **Let a equal 1; substituting gives a + 2 = 3.** | **`let a = 1`**<br>**`a + 2 = 3`** | Cite `a = 1`, substitute, check `1 + 2 = 3`, and store the accepted conclusion. |
| **Split into the cases x = 0 and x = 1.** | **`by cases:`**<br>`case x = 0:`<br>`case x = 1:` | Check coverage and prove the same target in both local branches. |
| **For natural n, define successor(n) = n + 1.** | **`have fn`** `successor(n N) N = n + 1` | Check the domain and return carrier, then make the definition callable. |

The recurring patterns are in the mathematical writing itself. The author supplies meaningful steps; Litex makes supported connections to the context executable.

## From mathematical language to checked knowledge

**Foundation.** Litex uses sets, elements, functions and relations. Familiar operations carry explicit conditions: `1 - 2 = -1`, while `1 / 0` is rejected as undefined. A function can put its required conditions directly in its domain:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

`reciprocal(0)` is rejected because its argument cannot meet the nonzero condition.

**Syntax.** Python-like indentation organizes scope and reasoning. In the universal statement above, `x R` introduces a real number, `x > 0` is the premise, and `x != 0` is the conclusion to check. Longer proofs still require authors to supply the mathematical route through intermediate facts, witnesses, induction or cases.

**Semantics.** Every statement must first be well-defined, then justified from its current context. The checker returns JSON describing its result, grounds and stored facts. For `1 + 1 = 2`, an English output excerpt is:

```json
{
  "statement_result": "accepted",
  "statement": "(1 + 1) = 2",
  "proof_method": { "type": "by_closed_calculation" },
  "stores": ["(1 + 1) = 2"]
}
```

For `1 / 0 = 0`, the result instead identifies the unmet condition `0 != 0`. Feedback is available in ten languages, including Chinese with `-lang zh`.

**Architecture: proof as search.** Consider:

```litex
let a = 1
a + 2 = 3
```

The first line stores `a = 1`. The second acts as a query: find that equality, substitute it to obtain `1 + 2 = 3`, and check the calculation. The accepted `a + 2 = 3` then becomes knowledge for later steps.

Litex is a fact-oriented mathematical verification language. Its native engine operates as a mathematics-specialized deductive knowledge base. Built-in mathematical rules provide reusable reasoning patterns; bounded contextual search finds relevant established facts and checks their conditions of use. Inference rules also record supported direct consequences of accepted facts, making them available to later steps.

Writing a fact therefore asks the system to find its grounds in the current mathematical context. Authors provide key intermediate facts, witnesses, cases or induction when needed; the system recovers the supported reasoning between those steps. Calculation is one available checking method. A search miss means that the checker could not justify the step, and does not prove its negation.

A proved `forall` becomes a reusable logical contract: later instances can be checked by matching its conclusion and verifying its premises, within the supported search paths and visible scope. Users extend the available knowledge by proving mathematics.

Its present mathematical semantics is set-based. The language and knowledge-management design, and the supported Lean proof-reconstruction backend, are separate layers; see the [technical positioning](docs/Manual.md#litex-theoretical-positioning).

```mermaid
flowchart TD
    A["Parse the next complete Statement<br/>Objects and Facts"] --> B["Check statement-specific obligations<br/>Ordinary facts: WD, then proof search"]
    C["Current context and native checks<br/>Definitions, facts, proved forall, built-in rules"] --> B
    B -->|accepted| D["Record evidence; store and infer<br/>Commit the statement's effects"]
    D -->|knowledge for later statements| C
    B -->|ordinary rejection| E["Discard this statement's effects<br/>Keep previously accepted context"]
```

**Native source snapshot — 2026-10-28.** These counts describe implementation branches and registered rule entries:

| Component | Count |
| --- | ---: |
| [Object (`Obj`) constructor branches](src/ast/obj.rs) | **150** |
| [Statement (`Stmt`) constructor branches](src/ast/stmt.rs) | **52** |
| [Atomic Fact variants](src/ast/fact/atomic.rs) | **74** |
| [Builtin verification rule entries](src/reading/rule_catalogue_generated.json) | **683** |

Constructor counts expand grouping enums and stop at payload structs; atomic facts include both polarities. The rule catalogue separately records **76 inference entries** and **526 explicit builtin theorem interfaces**. These are implementation counts, not a vocabulary to memorize or a count of independent axioms; they exclude user/library knowledge and other WD, calculator and strategy branches. See the [Manual's system pipeline](docs/Manual.md#system-pipeline) for the full flow and checking boundaries.

## Connect the same mathematics to other tools

The experimental `litex -lean -f proof.lit` compiler generates Lean statements and proofs that can be independently checked by Lean's kernel. This lets users write in Litex and connect supported mathematics to the Lean ecosystem.

The same source and verification records also support:

- **Interactive textbooks:** `litex -reading -f proof.lit` opens source with definitions, domains and proof references to explore, plus editing and checking.
- **LaTeX:** `litex -latex -f proof.lit` formats mathematical definitions and statements for documents.
- **C and Python:** experimental extraction turns supported computational definitions into runnable programs.

## Working with AI

A person or agent can propose a step, inspect its feedback, repair it and continue in the same Session. Earlier accepted definitions and facts remain available after an ordinary rejection.

A preliminary report from a plane-geometry library-building experiment with **165 mathematical tasks** and `deepseek-chat` records these elapsed times:

| Automatic library-building run | Litex | Lean |
| --- | ---: | ---: |
| Recorded elapsed time | **14.3 minutes** | **177.5 minutes** |

This report lacks paired completion counts and validation criteria, so these times alone do not establish a library-building speedup. Other projects include agent-written IMO geometry proofs and textbook developments in proof techniques, algebra, analysis and geometry.

## Try Litex

Use the website's playground, or install on macOS/Linux with Homebrew:

```bash
brew install litexlang/tap/litex
litex -e '1 + 1 = 2'
```

On Windows with Scoop and Git installed:

```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
```

Save any complete Litex example from the appendix as `proof.lit` and run `litex -strict -f proof.lit`. For interactive work:

```bash
litex -strict -session -e 'let a = 1'
```

Enter `a = 2`: it is rejected. Then enter `a + 2 = 3`: it succeeds using the retained context. Keep this Session open while writing; save accepted source and use a clean file run at checkpoints. `litex -help` lists commands.

Litex is in beta. `-strict` rejects user-written `trust` and `axiom`; verification still relies on Litex's checker and mathematical foundations.

## About

I am Jiachen Shen (沈嘉辰), a mathematics PhD student at Fudan University. I hope Litex helps more people write checkable mathematics and understand the definitions, conditions and reasoning behind it. Questions and feedback: litexlang@outlook.com.

Special thanks to Wei Lin, Siqi Sun, Peng Sun, Chenxuan Huang, Yan Lu, Sheng Xu, Hao wu, Keyao Zhu, and Zhaoxuan Hong for their support and advice.

Released under the Apache License 2.0.

## Appendix: complete examples

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
