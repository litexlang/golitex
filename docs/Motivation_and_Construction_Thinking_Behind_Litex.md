# Motivation and Construction Thinking Behind Litex

Jiachen Shen, October 21, 2026. The author typed the original Chinese draft himself.

Website: https://litexlang.com/

GitHub: https://github.com/litexlang/golitex

Litex starts from a question: can we write mathematics and get formal code directly? From an early age, we learn that mathematics is a rigorous language: each statement needs grounds to justify its correctness. If mathematics is already a rigorous language, why couldn't mathematics itself be a formal language? Could we design one whose writing closely resembles everyday mathematics, adding reasonable constraints to make it structured enough to support mechanical proof?

The observation here is that many everyday expressions in mathematical language already carry precise logical responsibilities:

- “Take any…” establishes the variables, their domains, and the quantifiers.
- “Assume…” introduces local premises and determines their scope.
- “There exists…such that…” requires a witness or other grounds for existence.
- “By definition…” requires the expression to satisfy the defining conditions.
- “Therefore…” requires the conclusion to follow from the current context.

Can we find a syntax that directly connects the objects, conditions, and reasoning steps of ordinary mathematical language with expressions in a formal language? Can we find an execution model that checks what we write and clearly explains why each statement holds?

Litex rethinks the relationship between mathematics, natural language, and code from first principles. It aims to make mathematics itself a formal language. My hope is that anyone who uses mathematics, from school students to AI engineers, can start from familiar mathematical expressions, learn a small number of language conventions, and use formal tools while understanding the grounds for their checks.

First, let us compare these mathematical expressions with code in Litex and Lean, a widely used formal language.

The Lean examples use `import Mathlib`.

| Mathematical expression and its responsibility | Litex | Lean |
| --- | --- | --- |
| **Take any real x, assume it is positive, and conclude it is nonzero** | `forall x R:` | `example (x : ℝ) (hx : x > 0) : x ≠ 0 := by` |
|  | `    x > 0` | `  exact ne_of_gt hx` |
|  | `    =>:` |  |
|  | `        x != 0` |  |
| **There is a real number whose square is 4; choose 2 as a witness** | `witness exist w R st {w^2 = 4} from 2` | `example : ∃ w : ℝ, w ^ 2 = 4 := by` |
|  |  | `  refine ⟨2, ?_⟩` |
|  |  | `  norm_num` |
| **By definition, 3 has the property of being above two** | `prop is_above_two(t R):` | `def isAboveTwo (t : ℝ) : Prop := t > 2` |
|  | `    t > 2` |  |
|  |  | `example : isAboveTwo 3 := by` |
|  | `by def $is_above_two(3)` | `  norm_num [isAboveTwo]` |
| **Check a calculation directly** | `1 + 1 = 2` | `example : (1 : Nat) + 1 = 2 := by` |
|  |  | `  rfl` |
| **Define and call a reciprocal function on the nonzero reals** | `have fn reciprocal(x R: x != 0) R = 1 / x` | `noncomputable def reciprocal (x : {y : ℝ // y ≠ 0}) : ℝ :=` |
|  | `reciprocal(2) = 1 / 2` | `  (x : ℝ)⁻¹` |
|  |  |  |
|  |  | `example : reciprocal ⟨2, by norm_num⟩ = (2 : ℝ)⁻¹ := by` |
|  |  | `  simp [reciprocal]` |
| **Membership and representation across number systems** | `1 $in Z` | `example : ((1 : ℕ) : ℤ) = (1 : ℤ) := by simp` |
|  | `1 $in R` | `example : ((1 : ℝ) : ℂ) = (1 : ℂ) := by simp` |
|  | `1 $in C` |  |
| **Define a set and check one member** | `have multiples_of_four power_set(N) = {a N: a % 4 = 0}` | `def multiplesOfFour : Set ℕ := {a \| a % 4 = 0}` |
|  | `4 $in multiples_of_four` |  |
|  |  | `example : (4 : ℕ) ∈ multiplesOfFour := by` |
|  |  | `  simp [multiplesOfFour]` |

Let us follow these examples to explain the thinking behind Litex's design. Litex aims to let people express mathematics as closely as possible to ordinary mathematical language, ideally with a direct correspondence between the source and the intended mathematics, while preserving rigor. (Formal tools can reduce the work of checking proofs, but this does not make them infallible. A statement written in Lean may fail to express the intended mathematical meaning, and semantic alignment is a problem the formalization community must address. See [Faults in Our Formal Benchmarking: Dataset Defects and Evaluation Failures in Lean Theorem Proving](https://arxiv.org/html/2606.29493v1#A5).)

The first question is choosing a suitable mathematical foundation and deciding what objects and operations mean. Lean uses type theory, and its mathematical libraries also choose explicit conventions for particular operations. For example, Lean/Mathlib extends real division to a total function, with `(1 : ℝ) / 0 = 0`; natural-number subtraction truncates at zero, so `(1 : Nat) - 2 = 0` (see [Division by zero in type theory: a FAQ](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)). These are choices of encoding and library design. Type theory can also express restricted domains, and Lean's integer subtraction satisfies `1 - 2 = -1`. But when familiar symbols carry different conventions, users need to check whether the formal statement still expresses the mathematics they intended.

To help more people learn and use Litex, I chose set theory as its foundation. Sets, elements, functions, and relations already belong to the way many people understand mathematics. These basic terms stay with us from secondary school into our working lives. From there, I wanted to bring the mathematical symbols people routinely write in LaTeX into the language, together with the relationships behind them. Recognizing an intersection symbol is only the beginning; the system also needs to understand how intersection relates to membership, inclusion, and equality. Here, `1 / 0` is rejected because it is not well-defined, while `1 - 2 = -1`.

With the mathematical vocabulary in place, the next question is syntax design. I want mathematical language itself to become formal code: write objects, definitions, conditions, and reasoning steps, and let each play its corresponding role in the language. More complex statements use indentation similar to Python. Let us expand two examples from the table to see exactly where this correspondence appears.

“Take any real number x, assume it is positive, and conclude that it is nonzero” can be written as:

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

`forall x R` corresponds to taking an arbitrary real number x. The premises of the current argument appear before `=>:`, and the conclusion to be proved follows it. Both the assumptions and x are scoped to this statement. The correspondence involves more than recognizing a few English words: position and indentation also express mathematical relationships.

Defining a reciprocal function on the nonzero real numbers and evaluating it at one argument can be written as:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

`have fn reciprocal` defines the function; `(x R: x != 0)` specifies a nonzero real argument; the following `R` specifies that the value is real; and `= 1 / x` gives the function value. At a call, the system must establish from the current context that the argument satisfies the domain conditions. `reciprocal(0)` cannot pass this check.

These two examples show the correspondence I want to preserve: mathematical objects, premises, domains, and reasoning steps each have an explicit place in the code. The intended correspondence concerns mathematical meaning, reasoning moves, and scope. Conditions and background knowledge omitted in ordinary mathematical writing still need to be supplied through explicit context or rules.

The examples above show how to write the mathematics. The second question from the opening is how the system checks it and tells me why it holds. Clear syntax is only the beginning; execution must connect each statement with its grounds.

When you enter `1 + 1 = 2`, Litex returns a result for that statement. The following excerpt shows the fields relevant to its explanation:

```json
{
  "statement_result": "accepted",
  "statement": "(1 + 1) = 2",
  "proof_method": {
    "type": "by_closed_calculation",
    "rule_name": "Closed calculation",
    "message": "Exact evaluation of closed expressions without proof search"
  },
  "stores": [
    "(1 + 1) = 2"
  ],
  "infers": []
}
```

When you enter `1 / 0 = 1 / 0`, the result identifies an unmet well-definedness condition. Again, this is an excerpt of the relevant fields:

```json
{
  "statement_result": "rejected",
  "statement": "(1 / 0) = (1 / 0)",
  "why_failed": {
    "phase": "well_defined",
    "goal": "<well_defined_not_proven>",
    "message": "Could not prove that the statement is well-defined.",
    "diagnostic": {
      "category": "well_defined",
      "message": "Could not prove that the statement is well-defined.",
      "obligation": "0 != 0",
      "expression": "(1 / 0)"
    }
  },
  "stores": [],
  "infers": []
}
```

The same process applies to the reciprocal function above. To check `reciprocal(2) = 1 / 2`, the argument must satisfy `2 != 0` before the function definition can be used to check the equality. Replacing it with `reciprocal(0)` leaves the required nonzero condition unmet. Checking an existential witness requires confirming that it belongs to the specified set and satisfies the stated properties. Checking `by def $is_above_two(3)` requires establishing the defining condition `3 > 2`.

I want the system to display these mathematical grounds directly. The output above explains that `1 + 1 = 2` was checked by the `Closed calculation` rule, while the division-by-zero example identifies the condition that cannot be met. Litex provides output in ten languages, including Chinese and English. Users write mathematical objects and steps; the checker returns the grounds it found, or identifies the conditions and proof evidence still missing. Structured verification records also need a presentation suited to their readers before they become clear teaching explanations.

> Further detail: Litex's `litex -session` interactive mode resembles Python's REPL: a failed statement leaves previously accepted definitions and facts available. It is like working on a scratchpad. A mistake leaves the accepted context intact; only accepted work becomes context for later input. For example, after accepting `let a = 2`, trying `a = 3` fails, but the same session can still use `a` to verify `a + 1 = 3`. The failed step is discarded and the accepted context remains. In a common Lean file workflow, an edit often triggers another round of the relevant checks; Litex makes incremental retention of accepted facts part of its interactive experience. This interaction is well suited to generating proofs in batches through collaboration between Litex and AI agents.

I want Litex to be like a strict teacher beside you: when a check succeeds, it explains the grounds; when it fails, it identifies what it could not prove. Failure to find a proof does not mean that the statement is mathematically false.

This choice shaped the verification engine. In a typical Lean tactic workflow, the author supplies instructions that construct a proof, which is ultimately checked by a kernel. Litex puts the next mathematical fact at the center of the interaction: given the current context, can the system justify this statement? This is a choice about the default writing experience. Lean's documentation describes its [elaboration and checking model](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/): in the common tactic workflow, the author supplies *how to prove* through tactics while Lean presents the remaining *what to prove* goals. Litex instead centers the proof on *what to prove*, expressed as mathematical steps, and asks its checker to explain *how* each supported step follows.

Litex has more than 600 built-in rules and a layered, recursive verification process for finding appropriate proof routes. Its vocabulary includes dozens of object forms, such as numbers like `1`, functions such as `+`, and set operations such as `union`; dozens of statement forms, including definitions such as `let a = 1`; and dozens of fact forms, including inequalities such as `1 < 2`, existential facts such as `exist x R st {x > 1}`, and universal facts such as `forall a Z => a $in R`. The verifier needs enough context. If you skip too many steps, its search engine may be unable to find or derive what you want to prove.

The basic logic of finding relevant facts in context and applying suitable rules to check each step is straightforward: matching and substitution. Find a relevant known fact, match it against the statement being checked, and determine whether the required substitutions and conditions hold. This idea developed into structured fact lookup, bounded recursive verification, built-in mathematical rules, and explicit statements for proof steps such as introducing witnesses or splitting into cases. At its core, this is a search engine highly specialized for mathematics.

With the built-in rules in place, the task is to read the user's input and determine which rules and contextual facts can establish it. Without the required context or an applicable rule, the system cannot prove the statement. For example, `a = 1` is `unknown` when I do not know what a is. After you introduce `let a = 1` and then enter `a = 1`, Litex can find the relevant context and prove `a = 1`.

There are many common mathematical object and statement forms, but they form a finite vocabulary to work with. One contribution I see in Litex is that, through two years of exploration, I have connected familiar relationships among objects and statements so that everyday mathematical expressions can correspond almost one for one to Litex statements. Familiar objects have definitions and relationships with other objects; these connections are captured in Litex's more than 600 built-in rules. Users should not have to manage all these trivial details themselves.

But checking a statement is only part of what I want. I also want an explanation of the verification: which facts it used, which rules connected them, and where a step could not be justified. Litex therefore has a search engine specialized for mathematics, operating on a database structure specialized for mathematics. Within its supported scope, it uses the context and built-in rules to find grounds for statements and report where verification fails.

![Litex verification pipeline](https://litexlang.com/assets/diagrams/litex-verification-pipeline-v2.png)

Turning familiar mathematical expressions, step by step, into knowledge that a machine can recognize, store, and reuse is difficult. This is the core of the Litex project and the work performed by its kernel, with more than 200,000 lines of Rust source. I spent two years exploring what I was building while building it; AI helped me work through the engineering details. Even as a programmer who relies on hundreds of keyboard shortcuts, I could not have built a project of this size without AI. To connect these expressions, their context, and their verification grounds, I developed Litex's mathematical database and search engine myself. The pipeline now checks statements and produces results explaining why they hold. This also suggests a use in mathematics education. We can build interactive textbooks in Litex source close to ordinary mathematical expression, with each verified statement connected to structured information about why it holds. Linking those records creates a network that helps readers understand how mathematical concepts connect. The experience could change how they think about mathematics, code, and proof.

A small age example makes this pipeline concrete. The same reasoning appears as Litex source, JSON explaining its grounds, and Lean generated by `-lean`. Compilation is currently a preview feature; the Lean column below contains excerpts from actual output.

| Litex source | JSON (verification summary) | Lean (`-lean` excerpt) |
| --- | --- | --- |
| `let my_age = 3` | `{` | `noncomputable def _object_i1 :=` |
| `let brother_age = 3 * my_age` | `  "statement_result": "accepted",` | `  Litex.number (M := M) (3 : ℂ)` |
| `brother_age = 3 * 3 = 9` | `  "statement": "brother_age = (3 * 3) = 9",` |  |
|  | `  "proof_method": {` | `theorem h_1 :` |
|  | `    "type": "compound_fact",` | `  Litex.Same (_object_i1 …)` |
|  | `    "rule_name": "Chain"` | `    (Litex.number … (3 : ℂ)) := …` |
|  | `  },` |  |
|  | `  "stores": [` | `-- … intermediate steps omitted …` |
|  | `    "brother_age = (3 * 3) = 9",` |  |
|  | `    "brother_age = (3 * 3)",` | `theorem h_470 :` |
|  | `    "(3 * 3) = 9"` | `  Litex.Same (_object_i2 …)` |
|  | `  ]` | `    (Litex.number … (9 : ℂ)) := …` |
|  | `}` |  |

The Litex source is the mathematics a person writes. The JSON records the machine's grounds for it, and the Lean code is the proof's form after connecting the result to Lean. An interactive textbook can use these verification records. For an independent check, the generated Lean proof can be checked as well.

Once verification produces a structured record, further possibilities emerge.
The relationships between definitions and established facts can support knowledge graphs. AI agents can use the feedback to revise a failed step and continue from accepted knowledge. Building a capable mathematical agent around this interaction is one of my longer-term goals.

The same record also provides a bridge to Lean. Litex has its own language and verification engine. Within the current compiler's supported scope, the source and verification records can be used to generate Lean statements and proofs that follow the reasoning Litex actually used. These can then be checked independently by Lean's kernel, providing an additional way to review Litex's verification results. This path is still being extended and does not yet cover all of Litex's language features and inference rules.

When writing mathematics, users can first check each step in Litex, inspect its justification, and revise steps that do not pass. Kernel checking of the generated Lean proof is a separate step. Litex's own checks use a database specialized for mathematics, fact lookup, and verification rules, and can provide quick feedback on some tasks. The following local spot check was recorded on October 21, 2026: Litex used `target/release/litex -f`, and Lean used `lake env lean` in a project with an existing Mathlib cache to check the same small examples. Lean's times are from a second, warmer run. This is not a formal benchmark; see the [Lean–Litex example comparison](Representative_Lean_Litex_Example_Comparisons.md#9-local-runtime-spot-checks) for detailed conditions and guidance on interpreting it fairly.

| Scenario | Litex (median) | Lean (2nd warmer run) | Approximate difference |
| --- | --- | --- | --- |
| Short arithmetic / `x = 2` ⇒ `x + 1 = 3`, `x^2 = 4` | ~6 ms | ~7 s | ~1000× |
| Calculation chain for two linear equations in two unknowns | ~16 ms | ~30 s | ~2000× |
| Sets: intersection preserves inclusion; `{1,2} ∈ {{}, {1,2}}` | ~4 ms | ~3.4 s | ~800× |
| Large witness `witness exist a, b, c, d N+ st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481` | ~5 ms | ~16–21 s (both `norm_num` and `native_decide` were slow) | ~3000×+ |
| Control: Lean's `1 + 1 = 2` without Mathlib | — | ~2.3 s (`lake env lean` startup alone) | Litex still takes only a few milliseconds for the whole file |

I see enormous value in compiling Litex to Lean. It gives Litex a path into the Lean ecosystem and adds an independent check on translated proofs. Many readers find Lean difficult to read, and some of its default semantics differ from ordinary mathematical expectations. Litex offers a route toward making formal tools more accessible: familiar expression and fast checking in Litex, with deeper libraries and independent kernel rechecking available through Lean. For more complete examples side by side, see the [Lean–Litex example comparison](Representative_Lean_Litex_Example_Comparisons.md); for the overall design, see the [Litex Blueprint](Litex_Blueprint.md).

Although AI is disrupting how mathematical research is evaluated, I think this is the best time to learn mathematics; 3Blue1Brown discusses this in [*There's never been a better time to go into math*](https://www.youtube.com/watch?v=LKrwhjOI8Nc). Most people do not need to conduct mathematical research. They need to use mathematics as a tool for understanding the world. To me, AI has not yet solved the problem of mathematical understanding: as a learning aid, it often feels like an electronic tutor focused on solving exercises. But AI has made it possible to build projects like Litex quickly. Litex revisits questions such as what mathematics is and what reasoning means from first principles. My hope is that, after learning Litex, readers will see mathematics written in ordinary language and think of Litex, and remember that mathematics itself is a rigorous language, with logic and connections behind it. That would be enough for me.

Litex is still under rapid development. Please try it and share your suggestions. To learn more about how Litex works, contact [litexlang@outlook.com](mailto:litexlang@outlook.com).
