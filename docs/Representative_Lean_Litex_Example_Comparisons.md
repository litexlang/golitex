# Comparing Litex and Lean: Constructing, Understanding, and Using Mathematical Knowledge

Created and maintained by Jiachen Shen.

[Try the examples](https://litexlang.com/doc/Representative_Lean_Litex_Example_Comparisons) ·
[Markdown source](https://github.com/litexlang/golitex/blob/main/docs/Representative_Lean_Litex_Example_Comparisons.md) ·
[中文](Lean与Litex示例对比.md)

A mathematical language shapes what an author writes, what a checker reconstructs,
and what another reader can understand and use. This comparison asks:

> **What does it cost to turn a mathematical idea into knowledge that can be
> checked, understood, repaired, and reused? Which parts of that work does
> Litex's design change?**

Litex investigates a fact-oriented language: authors introduce mathematical
objects and definitions, state facts, and supply meaningful proof steps;
the checker establishes supported connections from the accepted context.
The examples below make that division of labor visible. They motivate a
testable hypothesis about the cost of mathematical work. They do not yet
establish lower authoring or reading costs across tasks.

<a id="3-calculation-chains"></a>
<a id="direct-local-consequences"></a>
<a id="the-central-inversion-state-the-next-fact-reconstruct-its-grounds"></a>
<a id="constructing-knowledge"></a>

## 1. Construction: how directly does the source express the mathematical route?

Solve `2*x + 3*y = 10` and `4*x + 5*y = 14`. The mathematical choice is to
eliminate `x` by subtracting the second equation from twice the first:

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = (-4)
```

The source retains the elimination step and the substitution for `x`.
Litex checks each connection using the hypotheses and its algebraic rules.
The author chooses a useful calculation; the checker supplies the routine
justification. A longer argument still needs the author to choose its
intermediate facts, witnesses, estimates, or cases.

Lean can preserve the same route with `calc`:

```lean
import Mathlib

example (x y : ℝ)
    (h1 : 2 * x + 3 * y = 10)
    (h2 : 4 * x + 5 * y = 14) :
    y = 6 ∧ x = -4 := by
  have hy : y = 6 := by
    calc
      y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) := by linarith
      _ = 2 * 10 - 14 := by rw [h1, h2]
      _ = 6 := by norm_num
  have hx : x = -4 := by
    calc
      x = ((2 * x + 3 * y) - 3 * y) / 2 := by ring
      _ = (10 - 3 * 6) / 2 := by rw [h1, hy]
      _ = -4 := by norm_num
  exact ⟨hy, hx⟩
```

For completing the theorem with less visible derivation, Lean can also use:

```lean
import Mathlib

example (x y : ℝ)
    (h1 : 2 * x + 3 * y = 10)
    (h2 : 4 * x + 5 * y = 14) :
    y = 6 ∧ x = -4 := by
  constructor <;> linarith
```

These forms support different comparisons. Completion time should use each
system's effective native tools. A reading task can ask whether a reader can
recover the elimination argument from the source. Source length alone does
not answer either question: a short automation call can hide a long derivation,
while a longer calculation can deliberately expose it.

Litex's characteristic here is that the next mathematical fact is itself an
instruction to check. Lean also supports forward `have` proofs and automation;
its [elaborator constructs proof terms and its kernel checks them](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/).
The comparison concerns the author's interface and its costs, including how
much control the author wants over routine proof reconstruction.

<a id="8-a-design-perspective-what-the-author-states-what-the-checker-reconstructs"></a>
<a id="representative-leanlitex-example-comparisons"></a>
<a id="six-related-changes-of-starting-point"></a>
<a id="syntax-start-with-the-fact"></a>
<a id="why-the-combination-matters"></a>
<a id="comparison-dimensions"></a>

### Six questions to carry through the examples

| Mathematical activity | Comparison question | Existing material |
| --- | --- | --- |
| [Construct](#constructing-knowledge) | How much work lies between the mathematical route and accepted source? | Equation and estimate chains; witnesses. |
| [Preserve meaning](#meanings-and-domains) | How are operation meanings and conditions of use kept aligned with the intended problem? | Division, square roots, guarded functions. |
| [Accumulate knowledge](#objects-and-membership) | How does an object acquire properties and become usable in another context? | Numeric membership, subsets, intersections. |
| [Repair](#interaction-and-repair) | What does a failed attempt reveal, and what accepted work remains available? | Session interaction and structured feedback. |
| [Understand and reuse](#understanding-and-reuse) | Can someone else identify the route, respect its conditions, and continue the mathematics? | Convergence; a domain-preserving rational map; subject modules. |
| [Check repeatedly](#checking-performance) | How much checking can the workflow afford, and how does cost grow with dependencies? | Dated local runtime observations; witness checking. |

The sections establish concrete design behavior. [Evaluation](#evaluating-the-comparison)
separates that evidence from measurements still needed. Foundations, supported
scope, and trust remain explicit [conditions of the comparison](#trust-and-scope).

<a id="a-negative-input-to-a-real-square-root-function"></a>
<a id="division-by-zero"></a>
<a id="domains-carried-by-mathematical-objects"></a>
<a id="natural-number-subtraction"></a>
<a id="ordinary-mathematics"></a>
<a id="semantics-litex-follows-ordinary-mathematics"></a>
<a id="meanings-and-domains"></a>

## 2. Meaning: where are the conditions of mathematical use checked?

Writing a valid proof and expressing the intended mathematics are separate
obligations. Litex aims to keep familiar operation meanings and their domains
visible in the source. The useful comparison is whether that design helps
authors preserve the intended problem and recognize missing conditions.

### Division and guarded calls

For a reciprocal, Litex puts the nonzero condition in the definition domain:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

`reciprocal(0)` is outside that domain. Before accepting a fact using `1 / x`,
the checker must establish `x != 0` from the current context. Even
`1 / 0 = 1 / 0` fails well-definedness.

Mathlib deliberately extends standard real division at zero:

```lean
import Mathlib

example : (1 : ℝ) / 0 = 0 := by
  simp
```

Its [`div_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupWithZero/Basic.html#div_zero)
does not permit invalid cancellation: laws such as `x / x = 1` still require
nonzero hypotheses. Lean can also encode a restricted domain. The comparison
is where the condition is expressed, established, and consumed, and how much
work a user does to keep it aligned with the intended mathematics.

The same question appears in user-defined conditions:

```litex
have fn nonnegative_input(x R: x >= 0) R = x

forall x R:
    x >= 0
    =>:
        nonnegative_input(x) = x
```

One Lean interface packages the value and evidence in a subtype:

```lean
import Mathlib

def nonnegativeInput (x : {y : ℝ // 0 ≤ y}) : ℝ := x.val

example (x : ℝ) (h : 0 ≤ x) : nonnegativeInput ⟨x, h⟩ = x := by
  rfl
```

Litex checks the existing condition about `x` at the call. The subtype interface
passes a value together with a proof. Lean can instead use a separate proof
argument, and automation can assist either approach. A useful task measures
the work required to make legal calls, diagnose illegal ones, and modify a
domain while preserving the original specification.

### Subtraction and real square roots

Lean's natural-number subtraction truncates at zero:

```lean
example : (1 : Nat) - 2 = 0 := by
  decide
```

Litex keeps ordinary integer-valued subtraction for this expression:

```litex
1 - 2 = -1
1 - 2 $in Z
```

Lean's `Int` also gives `1 - 2 = -1`; the issue is selecting the intended
operation. See [`Nat.sub`](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/#Nat.sub).

Mathlib's real square root returns zero on negative inputs:

```lean
import Mathlib

example : Real.sqrt (-1) = 0 := by
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)
```

Litex requires a nonnegative input to its real square root:

```litex
have fn real_root(x R: x >= 0) R = sqrt(x)
real_root(4) = 2
```

`sqrt(-1) = 0` therefore fails well-definedness in Litex. Mathlib's
[`Real.sqrt_eq_zero_of_nonpos`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Sqrt.html#Real.sqrt_eq_zero_of_nonpos)
records a deliberate extension; its square-root identities retain the relevant
domain hypotheses. These are observable semantic choices. Whether one interface
reduces specification mistakes requires tasks that independently fix the
intended meanings, alongside legal controls to measure unnecessary rejection.

<a id="5-set-theoretic-objects-at-the-surface"></a>
<a id="intersections-preserve-inclusion"></a>
<a id="objects-knowing-a-property-and-packaging-a-subtype"></a>
<a id="objects-and-membership"></a>

## 3. Objects: how does mathematical knowledge accumulate?

In Litex, facts about one source object can grow:

```litex
have a N = 1
a $in Z
a $in R
a $in C
```

The number has not been replaced at each line. Its membership in successive
number sets becomes available to later checks. This makes object identity and
accumulating mathematical knowledge part of the source model.

Lean organizes representations through types and embeddings. For example:

```lean
import Mathlib

example : ((1 : ℝ) : ℂ) = (1 : ℂ) := by
  simp
```

The real and complex values agree after the embedding. A comparison can follow
one value through several interfaces and count the conversions, auxiliary
evidence, and repair work each interface requires. It should also assess the
guarantees and generality those representations provide.

Sets give another concrete instance:

```litex
{1, 2} $in {{}, {1, 2}}

{1, 2} $subset {1, 2, 3}
{1, 2} $in power_set({1, 2, 3})

forall A, B set, x A:
    A $subset B
    =>:
        x $in B
```

```lean
import Mathlib

example : ({1, 2} : Set ℕ) ∈ ({∅, {1, 2}} : Set (Set ℕ)) := by
  simp

example : ({1, 2} : Set ℕ) ⊆ ({1, 2, 3} : Set ℕ) := by
  simp

example {α : Type} {A B : Set α}
    (hAB : A ⊆ B) {x : α} (hx : x ∈ A) :
    x ∈ B := by
  exact hAB hx
```

The Litex source uses sets and membership directly. The Lean source identifies
ambient carriers with `Set ℕ`, `Set (Set ℕ)`, and the type parameter `α`.
In Litex, `forall x S` introduces membership in `S`; `forall A set` introduces
a set parameter, not an element of a universal set of all objects.

### Using known facts by their mathematical content

If `s` is contained in `t`, intersecting both with `u` preserves inclusion:

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

A concise elementwise Lean proof is:

```lean
import Mathlib.Data.Set.Lattice

example {α : Type*} (s t u : Set α) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  intro x hx
  exact ⟨h hx.1, hx.2⟩
```

Litex's checker supplies the routine membership decomposition and transport.
The Lean proof makes that argument explicit through `hx` and the pair it
constructs. Both can also use named theorems where useful. The question is
how authors access relevant knowledge: by stating the needed fact, naming a
result, selecting automation, or supplying an explicit route, and how reliably
that continues to work as the context grows.

This is a source-interface comparison. Generated Lean still has types and
requires certified representation bridges; see [the semantic boundary](#semantic-representation).

<a id="interaction-and-repair"></a>

## 4. Repair: what happens after a candidate fails?

The [Agent Guide](AgentGuide.md) gives a small Session example. Start in a
directory without a project configuration; the failure output below is abbreviated:

```text
$ litex -lang en -strict -session -e 'have a R = 2'
litex> a = 3
{"run_result": "failure", "target": "repl", "errors": [{"phase": "...", "category": "...", ...}], "session_terminated": false, "termination": null}
litex> a + 1 = 3
{"run_result": "success", "target": "repl", "statement_results": [...], "errors": [], "session_terminated": false, "termination": null}
```

The rejected equality does not erase the declaration or `a = 2`. The next
statement can use the accepted context. A new process would need that context
loaded or replayed. The transaction unit is one statement; several pasted
statements can commit separately. Hard errors or replacing a committed
declaration can require a restart.

Checking also returns information about its mathematical effect. For
`1 + 1 = 2`, the normal statement result includes:

```json
{
  "statement_result": "accepted",
  "statement": "(1 + 1) = 2",
  "proof_method": {
    "type": "by_closed_calculation",
    "rule_name": "Closed calculation",
    "message": "Exact evaluation of closed expressions without proof search"
  },
  "stores": ["(1 + 1) = 2"],
  "infers": []
}
```

`proof_method` identifies the checking route; `stores` and `infers` describe
published facts. Failure feedback distinguishes stages and, where retained,
the relevant obligation: `1 / x` can fail because `x != 0` has not been
established. A proof-search miss does not establish that the proposed fact is
false. The [CLI reference](cli.md#json-output-contract) owns the output contract.

This makes a concrete propose–check–revise loop available to humans and
agents. The [Python Session driver](../examples/agent_session_demo/README.md)
demonstrates rejection followed by continued dependent work. It is a
deterministic interaction example, not a study of AI proving success.

Lean also supports [incremental elaboration](https://lean-lang.org/doc/reference/latest/releases/v4.9.0/),
proof-state inspection, and automation such as [`grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic).
A useful comparison gives both sides their normal interactive tools. Measure
diagnosis accuracy, accepted work reprocessed, repair attempts, total time and
tokens, and whether the repaired result still answers the original problem.
Improved acceptance alone can hide a changed target or an added assumption.

<a id="1-direct-facts-short-estimates-and-typed-domains"></a>
<a id="2-scalar-multiplication-preserves-convergence"></a>
<a id="ai-lowers-generation-cost-not-automatically-understanding-cost"></a>
<a id="keep-the-mathematical-estimate-visible"></a>
<a id="understanding-and-reuse"></a>

## 5. Understanding and reuse: what can the next reader do with the result?

A checked result becomes useful knowledge when another person can understand
its conditions and use it in a further argument. Litex's source retains
mathematical choices; its checking record supplies a second view of their
justification. Whether this helps a new reader is an empirical question.

### Conditions travel with the construction

Consider `f(x) = (x+1)/(x-1)` for `x != 1`. To prove `f(f(x)) = x`, one must
first establish `f(x) != 1`, so that the second call is legal. The maintained
[Litex source](../lean/examples/real_mobius_involution/statement.lit) is:

```litex
forall x R:
    x!=1
    =>:
        x-1!=0

have fn mobius(x R:x!=1) R=(x+1)/(x-1)

forall x R:
    x!=0
    =>:
        2/x!=0

thm mobius_preserves_domain:
    ? forall x R:
        x!=1
        =>:
            mobius(x)!=1
    mobius(x)=(x+1)/(x-1)
    mobius(x)-1=2/(x-1)
    2/(x-1)!=0

thm mobius_involution:
    ? forall x R:
        x!=1
        =>:
            mobius(mobius(x))=x
    mobius(x)!=1
    mobius(x)-1!=0
    mobius(x)=(x+1)/(x-1)
    ((x+1)/(x-1))-1!=0
    mobius(mobius(x))=(mobius(x)+1)/(mobius(x)-1)=((x+1)/(x-1)+1)/((x+1)/(x-1)-1)=x
```

The reusable result `mobius_preserves_domain` supplies the condition consumed
by `mobius_involution`. This connects definition, domain preservation, and
subsequent use in one development. A reader can be asked to identify the
excluded point, explain the second call, or apply the map again.

The maintained [native Lean baseline](../showcases/litex_to_lean_adapter/DirectLean.lean)
also proves both properties concisely:

```lean
import Mathlib

noncomputable def mobius (x : ℝ) : ℝ := (x + 1) / (x - 1)

theorem mobiusInvolution (x : ℝ) (hx : x ≠ 1) :
    mobius x ≠ 1 ∧ mobius (mobius x) = x := by
  unfold mobius
  constructor
  · intro h
    field_simp [sub_ne_zero.mpr hx] at h
    linarith
  · field_simp [sub_ne_zero.mpr hx]
    ring
```

The [integration showcase](../showcases/litex_to_lean_adapter/README.md)
follows supported Litex output through an Adapter into ordinary Lean theorems.
It demonstrates a handoff path with actual representation and maintenance
costs. It does not establish a shorter proof or unrestricted compilation.

### A visible mathematical choice in analysis

For scalar multiplication of a convergent sequence, the useful choice is a
smaller tolerance. In the [full example](#convergence-example), Litex chooses
`epsilon / (|c| + 1)`, obtains a cutoff, and writes the resulting estimate.
The denominator stays positive, including when `c = 0`. The retained Lean
proof chooses `epsilon / |c|` and treats zero separately; Lean can use the
uniform argument too. The difference between those choices must not be
attributed to the languages.

A reading comparison can ask someone to recover that choice, explain why the
denominator is legal, and adapt the estimate. Producing a proof and understanding
one are separate tasks; a model's ability to generate source does not measure
another reader's comprehension.

### From individual results to a mathematical development

The [subject collection](../showcases/math_concepts_in_litex/README.md) provides
bounded developments, including a
[square-function derivative](../showcases/math_concepts_in_litex/7_calculus/README.md)
and a [coordinate-geometry library](../showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/README.md).
These support comparisons that include defining concepts, building lemmas,
using a construction, changing a condition, and handing the result to another
author. Their dated Litex checks do not certify all corresponding Lean analogy
files or an entire mathematical subject.

Measure knowledge construction and consumption separately: the effort to
establish an interface, then the effort for a new user to apply it. Record
library development, any checker changes, and adapter work rather than treating
them as free. This distinguishes a generally usable language mechanism from
a collection of examples supported by task-specific implementation work.

<a id="4-witnesses-contradiction-and-counterexamples"></a>
<a id="9-local-runtime-spot-checks-informal"></a>
<a id="a-concrete-witness"></a>
<a id="checking-performance"></a>

## 6. Performance: how much checking can the workflow afford?

Checking latency matters when every candidate statement can receive feedback.
A large speed difference can change the cost of interactive experimentation,
agent search, or checking each step in an interactive textbook. These are
workflow hypotheses to test; checker speed alone does not establish their
effect on completed mathematics.

<a id="loaded-checking-comparison"></a>

### Common tasks: roughly 10–100× checking differences after startup and imports

**On some common mathematical tasks, Litex can check a statement roughly
10–100× as fast as Lean.** In a local measurement on 2026-10-23, the selected
examples below showed differences of about 12–77×, with process startup and
`import Mathlib` already excluded.

For example, prove that the sum of any two positive real numbers is positive:

```litex
forall x,y R:
    x > 0
    y > 0
    =>:
        x+y > 0
```

The corresponding Lean proof can reference the theorem directly:

```lean
import Mathlib

example : ∀ x y : Real, 0 < x → 0 < y → 0 < x+y := by
  intro x y hx hy
  exact add_pos hx hy
```

Litex's detailed verification record uses the builtin strategy
`PosAddPosIsPos`. Checking this complete universally quantified statement
took a median **0.394 ms** in Litex. The direct Lean `add_pos` proof took
**9.305 ms**, a ratio of **23.60×**. The measured `linarith` proof of the same
goal took 14.923 ms; the table uses the faster direct theorem proof.

The table selects common examples from this batch where Litex was faster.
Each Lean entry uses the fastest successful route tested for that task,
including direct theorems and compact proof terms. Times are median
milliseconds; ratios use the unrounded medians.

| Complete mathematical task | Litex | Lean | Lean/Litex | Fastest Lean route tested |
| --- | ---: | ---: | ---: | --- |
| Sum of two positive reals is positive | 0.394 | 9.305 | **23.60×** | `add_pos` |
| Product of two positive reals is positive | 0.408 | 4.986 | **12.23×** | `mul_pos` |
| Every real square is nonnegative | 0.597 | 13.491 | **22.60×** | `sq_nonneg` |
| Reciprocal of a positive real is positive | 0.287 | 8.167 | **28.43×** | `one_div_pos.mpr` |
| A zero real product has a zero factor | 0.203 | 6.860 | **33.83×** | `mul_eq_zero.mp` |
| Witness that the positive-real set is nonempty | 0.084 | 6.439 | **76.88×** | Explicitly typed `⟨1, zero_lt_one⟩` |

This batch used one macOS arm64 workstation, release Litex 1.1.2-beta, and
Lean/Mathlib 4.31.0. Every Litex file passed independently in strict mode;
each successful Lean route also passed in an ordinary independent file
without `sorry`. Each Litex case has 90 warm samples across three processes;
each Lean route in this table has 21 across three processes. First checks
were recorded separately and excluded from these medians.

Litex's interval includes tokenization, parsing, well-definedness, verification,
and storage of the complete statement, with fresh Runtime construction outside
the interval. Lean's interval includes command elaboration, proof construction,
and synchronous kernel checking, with command parsing outside. Both exclude
startup, dependency imports, and result output. These measure the respective
checking paths, rather than isolated kernel reduction, and exclude compiling
Litex into Lean and rechecking it. The workstation had no CPU isolation or
controlled cache clearing. These selected local results are not an overall
ratio across tasks and do not yet establish a proportional reduction in
authoring time.

The [unscreened summation and context-load comparison](../examples/litex_vs_lean_speed/search-and-expansion.md)
retains all six cases; Lean's direct route was faster in five. Proof route and
context load can change the comparison result.

<a id="9-local-runtime-spot-checks"></a>

### Whole-process observations, 2026-10-21: including startup and loading

The existing local spot check on Apple Silicon recorded the following results.
Litex used a built `target/release/litex -f`. Lean used `lake env lean` in
`showcases/litex_to_lean_adapter`, with Mathlib olean caches already present.
Litex times are medians over repeated runs; Lean times are a second, warmer
run. This subsection preserves those whole-command observations; they must
not be mixed with the startup- and import-excluded timings above.

| Scenario | Litex (median) | Lean (2nd warmer run) |
| --- | --- | --- |
| Short arithmetic / `x = 2` ⇒ `x + 1 = 3`, `x^2 = 4` | ~6 ms | ~7 s |
| Two-equation calculation chain | ~16 ms | ~30 s |
| Sets: intersection preserves inclusion | ~4 ms | ~3.4 s |
| Positive-integer witness `(95800,217519,414560,422481)` for `a^4+b^4+c^4=d^4` | ~5 ms | ~16–21 s (`norm_num` / `native_decide`) |
| Control: Lean `1 + 1 = 2` with no Mathlib | — | ~2.3 s (`lake env lean` startup) |

These data record historical whole-command latency and do not establish a
checker speedup. Startup and loading can dominate short proofs, and the two
columns use different sampling summaries. The observations do not isolate
proof search or cover an editor's already-loaded incremental checking.
Litex performs exact closed calculation and contextual checking directly;
Lean tactics such as `norm_num` construct
proof terms for kernel checking. These are different checking architectures
and trust boundaries, not identical engines running at different speeds.

### A supplied witness: checking and discovering are separate costs

The following numbers give a counterexample to Euler's sum-of-powers conjecture
for fourth powers: three positive fourth powers equal another positive fourth
power,

\[
95800^4 + 217519^4 + 414560^4 = 422481^4.
\]

Litex states the supplied witness and checks its membership and equation:

```litex
witness exist a, b, c, d N+ st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481
```

The corresponding Lean proof supplies the same numbers:

```lean
import Mathlib

example : ∃ a b c d : ℕ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4 := by
  refine ⟨95800, 217519, 414560, 422481, ?_⟩
  norm_num
```

The runtime row concerns verification of this supplied witness. It does not
measure finding the numbers or rebuilding the historical disproof.

### Measurements that would explain the workflow effect

| Measurement | What it answers |
| --- | --- |
| Fresh process, including dependencies | Cost of checking a standalone candidate or file. |
| New statement in a resident interactive process | Latency of repeated propose–check–revise steps. |
| Growing context and dependency depth | Whether lookup, loading, and rechecking remain affordable. |
| Complete task under a fixed budget | How checking time combines with generation, search, repair, and completion. |
| Required independent checking | Total source checking, proof generation, adapter, and backend-checking cost. |

The two sets of results above give whole-command times for new processes and
single-statement checking times after startup and imports. Resident editor
interaction, growing contexts, and complete authoring tasks still need separate
measurement. These numbers do not imply the same multiplier in AI success or
throughput. Broader benchmarks should freeze source and tools, retain raw
commands and inputs, use consistent repetition, report variation and memory,
and include unsuccessful cases.

<a id="a-research-hypothesis-that-can-be-tested"></a>
<a id="reading-the-comparison-fairly"></a>
<a id="evaluating-the-comparison"></a>

## 7. Evaluation: connect design differences to mathematical work

The demonstrated interface differences suggest a hypothesis: fact-oriented
source, explicit conditions, local feedback, and low checking latency may
reduce the cost of building and using checked mathematical knowledge. The
examples and local timing observations do not yet establish that combined
effect. No controlled authoring, model-success, or human-reading results are
reported on this page.

| Dimension | Suggested outcome to measure |
| --- | --- |
| Construction | Correct completion under a common budget; author time, theorem searches, auxiliary source, and model/tool calls. |
| Intended meaning | Whether domains, quantifiers, assumptions, and conclusions match an independently fixed mathematical task. |
| Accumulating knowledge | Work to reuse one object or result across contexts, including conversions and supporting evidence. |
| Repair | Time and attempts to repair a failure while preserving the intended statement; unnecessary changes to correct source. |
| Understanding and reuse | A new reader's accuracy and time identifying conditions, explaining the route, finding errors, and completing a downstream task. |
| Checking capacity | Latency, total time, memory, and correct completions per total budget at several dependency scales. |

Use two distinct library conditions. Matched mathematical background helps
study the interface; each system's available ecosystem measures current
practical cost. Report both rather than attributing a library difference to
language design. The [prime-number example](#prime-example) shows why:
the Litex proof receives background facts as premises, while the Lean proof
uses Mathlib's proved library results.

For a focused first comparison, use the equation chain for construction and
latency, the Möbius map for conditions and repair, and the square-function
derivative for a definition–lemma–application development. Freeze equivalent
mathematical requirements before testing, and permit normal Lean automation
and incremental tools. Count failures and unsupported tasks, and report setup
and library-building costs separately from repeated use.

Small kernels, proof terms, dependent types, library size, and community
experience answer important questions about trust, expressiveness, and
ecosystem maturity. Relate those properties to the tasks they affect. Likewise,
evaluate Litex's direct facts and fast checking by the work they enable.
That keeps the comparison tied to mathematical outcomes rather than a feature
inventory or a contest over the shortest source.

<a id="7-a-technical-boundary-facts-are-not-first-class-objects"></a>
<a id="a-semantic-difference-behind-the-syntax-eq-and-same"></a>
<a id="foundations-a-different-starting-point-not-only-shorter-code"></a>
<a id="start-here-syntax-semantics-objects-and-foundations"></a>
<a id="syntax-semantics-and-foundations"></a>
<a id="trust-and-scope"></a>

## 8. Foundations, supported scope, and trust

Litex is an experimental project in beta. Its set-oriented source model and
Lean's dependent type theory organize objects, propositions, and proofs
differently. Mathlib's operation conventions above are library choices, not
consequences forced by dependent type theory. Litex separates objects and facts;
Lean also supports general proposition and proof programming. Compare the
mathematics and interfaces actually needed by a task, including unsupported
forms and the work needed to extend them.

For Litex-only checking, the Rust verifier and its builtin and inference rules
remain part of the trusted implementation. `-strict` excludes source `trust`
and user axioms; it does not independently prove the verifier correct. Source
examples, rule audits, and independent checks establish different kinds of
evidence and should be reported separately.

The current `-lean -f` compiler replays supported typed execution evidence.
The [compiler guide](Litex_To_Lean_Compiler_Guide.md) describes its coverage,
explicit semantics parameters, models, and representation bridges. An ordinary
Lean theorem obtained through a reviewed Adapter is stronger integration
evidence than a generated theorem whose semantic assumptions have not been
instantiated. Neither establishes a complete Lean interpretation of all Litex.

<a id="semantic-representation"></a>

### Source identity and backend representation

The membership example preserves one source object while facts accumulate.
In supported Lean replay, `Litex.Same` records semantic equality between
certified representations, and `Litex.In` records membership. Generated Lean
is still typed. Recovering native Lean equality requires the appropriate
faithful representation bridge; heterogeneous semantic equality is not a
global conversion to Lean's `Eq`. The
[semantic interface](../lean/Litex.lean) and compiler guide own these contracts.

For either language, proof validity and correspondence to the intended
mathematics need separate attention. Lean's
[proof-validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
also distinguishes them. A performance or usability result must state which
checking guarantees and mathematical assumptions were required.

<a id="contraposition-by-contradiction"></a>
<a id="supporting-examples"></a>

## Further worked examples

The following retained examples extend the comparison beyond the opening
calculation. Each has a specific role: a visible tolerance choice, differing
background-library assumptions, or an explicit counterexample.

<a id="convergence-example"></a>

### Scalar multiplication preserves convergence

Both proofs obtain a tail bound for a smaller positive tolerance and reuse
the cutoff. The Lean proof uses `epsilon / |c|` and splits off `c = 0`:

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

The Litex proof instead chooses `epsilon / (|c| + 1)`:

```litex
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            |s(n) - a| < epsilon

prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}

thm converges_to_mul_const:
    ? forall s, scaled fn(n N) R, a, c R:
        $converges_to(s, a)
        forall n N:
            scaled(n) = c * s(n)
        =>:
            $converges_to(scaled, c * a)
    claim:
        ? forall epsilon R+:
            exist N0 N st {$is_eventually_close(scaled, c * a, epsilon, N0)}
        |c| >= 0
        |c| + 1 > 0
        have scale R+ = |c| + 1
        epsilon / scale > 0
        epsilon / scale $in R+
        |c| <= scale
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / scale, K)}
        witness exist K N st {$is_eventually_close(scaled, c * a, epsilon, K)} from N0:
            claim:
                ? forall n N:
                    n >= N0
                    =>:
                        |scaled(n) - c * a| < epsilon
                scaled(n) = c * s(n)
                |s(n) - a| < epsilon / scale
                |s(n) - a| >= 0
                scaled(n) - c * a = c * s(n) - c * a = c * (s(n) - a)
                |scaled(n) - c * a| = |c * (s(n) - a)| = |c| * |s(n) - a|
                |c| * |s(n) - a| <= scale * |s(n) - a|
                scale * |s(n) - a| < scale * (epsilon / scale) = epsilon
                |scaled(n) - c * a| = |c| * |s(n) - a| <= scale * |s(n) - a| < epsilon
            by def $is_eventually_close(scaled, c * a, epsilon, N0)
    by def $converges_to(scaled, c * a)
```

The witness, positivity facts, and inequality chain make the argument's
mathematical choices available for inspection. Routine links are checked from
context. This supports a reading and modification task, with the same
mathematical route supplied on both sides when isolating interface effects.

<a id="6-case-study-infinitely-many-primes"></a>
<a id="prime-example"></a>

### Infinitely many primes: keep background knowledge visible

Euclid's argument forms a factorial plus one, obtains a prime divisor, and
shows that the divisor exceeds the original bound. The Litex example receives
three general background results as premises: divisibility of the product,
existence of a prime divisor, and the product's lower bound.

```litex
have fn factorial_factor(x N+) N+ = x

# `$prime(a)` is native. Its symbolic contract is `2 <= a` together with
# `a % b != 0` for every `b` in `range(2, a)`.

claim:
    ? forall a N+:
        forall n, d N+:
            d <= n
            =>:
                product(1, n, factorial_factor) % d = 0
        forall n N+:
            2 <= n
            =>:
                exist k N+ st {$prime(k), n % k = 0}
        forall n N+:
            n <= product(1, n, factorial_factor)
        2 <= a
        =>:
            exist k N+ st {k > a, $prime(k)}
    product(1, a, factorial_factor) $in N+
    product(1, a, factorial_factor) $in R
    2 <= a <= product(1, a, factorial_factor) <= product(1, a, factorial_factor) + 1
    product(1, a, factorial_factor) + 1 $in N+
    2 <= product(1, a, factorial_factor) + 1
    obtain k from exist k N+ st {$prime(k), (product(1, a, factorial_factor) + 1) % k = 0}
    by cases:
        ? k > a
        case k <= a:
            product(1, a, factorial_factor) % k = 0
            2 <= k
            (product(1, a, factorial_factor) + 1) % k = (product(1, a, factorial_factor) % k + 1 % k) % k
            1 % k = 1
            (0 + 1) % k = 1 % k = 1
            (product(1, a, factorial_factor) + 1) % k = (product(1, a, factorial_factor) % k + 1 % k) % k = (0 + 1) % k = 1
            (product(1, a, factorial_factor) + 1) % k != 0
            impossible (product(1, a, factorial_factor) + 1) % k = 0
        case k > a:
            k > a
    witness exist prime_larger N+ st {prime_larger > a, $prime(prime_larger)} from k
```

The Lean example uses Mathlib's factorial and prime-divisor theorems:

```lean
import Mathlib

example (N : ℕ) : ∃ p ≥ N, Nat.Prime p := by
  have hN0 : 0 < Nat.factorial N := Nat.factorial_pos N
  have hN_ne_one : Nat.factorial N + 1 ≠ 1 := by omega
  obtain ⟨p, hp, hpN⟩ :
      ∃ p : ℕ, Nat.Prime p ∧ p ∣ Nat.factorial N + 1 :=
    Nat.exists_prime_and_dvd hN_ne_one
  use p
  constructor
  · by_contra hlt
    have hp_le_N : p ≤ N := by omega
    have hp_dvd_factorial : p ∣ Nat.factorial N :=
      (Nat.Prime.dvd_factorial hp).2 hp_le_N
    have hp_dvd_one : p ∣ 1 := by
      have hp_dvd_sum : p ∣ (Nat.factorial N + 1) - Nat.factorial N :=
        Nat.dvd_sub hpN hp_dvd_factorial
      simpa using hp_dvd_sum
    exact Nat.Prime.not_dvd_one hp hp_dvd_one
  · exact hp
```

The Litex claim checks the conditional argument under its listed premises;
it does not construct those background results. These examples expose two
routes through the same Euclidean idea, but their assumptions are not a
matched basis for a language-efficiency benchmark. Include the cost of
establishing equivalent background knowledge in any full comparison.

<a id="a-set-counterexample"></a>
<a id="set-counterexample"></a>

### A counterexample that another reader can recover

The natural number `2` distinguishes the even numbers from the multiples of `4`:

```litex
have multiples_of_four power_set(N) = {a N: a % 4 = 0}
have multiples_of_two power_set(N) = {a N: a % 2 = 0}
by contra:
    ? multiples_of_four != multiples_of_two
    2 $in multiples_of_two
    2 $in multiples_of_four
    impossible 2 % 4 = 0
```

```lean
import Mathlib

example : ({a : ℕ | a % 4 = 0} : Set ℕ) ≠
    {a : ℕ | a % 2 = 0} := by
  intro h
  have h2 : (2 : ℕ) ∈ ({a : ℕ | a % 2 = 0} : Set ℕ) := by
    norm_num
  have h4 : (2 : ℕ) ∈ ({a : ℕ | a % 4 = 0} : Set ℕ) := by
    rw [h]
    exact h2
  norm_num at h4
```

Both sources expose the decisive element and contradictory membership.
A review task can ask the reader to identify and reuse that counterexample;
token count does not measure whether they succeeded.

<a id="further-reading"></a>

## Further reading

- [Litex Blueprint](https://litexlang.com/doc/Litex_Blueprint): broader language-design argument and the group-identity example.
- [Manual](Manual.md) and [CLI reference](cli.md): supported language, trust, and interaction contracts.
- [Agent Guide](AgentGuide.md): persistent Session and restart boundaries.
- [Math-concept developments](../showcases/math_concepts_in_litex/README.md): definitions, constructions, and downstream consumers.
- [Litex-to-Lean compiler guide](Litex_To_Lean_Compiler_Guide.md) and [integration showcase](../showcases/litex_to_lean_adapter/README.md): supported replay and ordinary Lean interfaces.
