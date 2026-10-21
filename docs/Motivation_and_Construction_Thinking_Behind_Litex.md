# Motivation and Construction Thinking Behind Litex

Jiachen Shen, October 21, 2026. The author wrote the Chinese original of this essay himself.

Litex starts from a question: can we write mathematics and get formal code directly? From an early age, we learn that mathematics is a rigorous language: each statement needs grounds to justify its correctness. If mathematics is already a rigorous language, why couldn't mathematics itself be a formal language? Could we design one whose writing closely resembles everyday mathematics, adding reasonable constraints to make it structured enough to support mechanical proof?

This is an attempt to rethink the relationship between mathematics, natural language, and code from first principles. Litex grew out of that curiosity. It aims to make mathematics itself a formal language, so that anyone who uses mathematics, from school students to AI engineers, can also use formal tools directly, without specialized training.

Here is the thinking behind Litex's design.

The first question is choosing a suitable mathematical foundation and its axioms. Every formal language relies on particular mathematical axioms, and the choice of foundation directly shapes the language. Consider Lean as a point of comparison. Lean uses type theory, an abstract and coherent mathematical foundation supporting a powerful, programmable system. Some of its default conventions differ substantially from everyday mathematics. For example, Lean/Mathlib extends real division to a total function, with `(1 : ℝ) / 0 = 0`; natural-number subtraction truncates at zero, so `(1 : Nat) - 2 = 0` (see [Division by zero in type theory: a FAQ](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)). Such choices can leave people thinking they have proved A when they have actually proved a slightly different B, because familiar mathematical notation may mean something different in Lean. This can make learning and using formal tools feel out of reach for ordinary users.

To help more people learn and use Litex, I chose set theory as its foundation. Sets, elements, functions, and relations already belong to the way many people understand mathematics. These basic terms stay with us from secondary school into our working lives. From there, I wanted to bring familiar mathematical notation—the symbols people routinely write in LaTeX—into the language, together with the mathematical relationships behind it. Recognizing an intersection symbol is only the beginning; the system also needs to understand how intersection relates to membership, inclusion, and equality. Here, `1 / 0` is rejected because it is not well-defined, while `1 - 2 = -1`. Real square roots provide another example: `Real.sqrt (-1) = 0` holds in Mathlib, whereas Litex requires a nonnegative input before accepting a fact involving `sqrt`. In ordinary real mathematics, a negative number has no square root; I do not want the language to assign it a default value.

With the mathematical vocabulary in place, the next question is syntax design. I want mathematical language itself to become formal code. Statements such as `1 + 1 = 2` and `forall x, y R: x >= 0 and y >= 0 => x + y >= 0` can run directly in Litex. More complex mathematical statements are organized using syntax similar to Python's. Users write what they want to prove, and Litex explains whether it can justify the statement, and why.

The same small calculation can be written in Lean as:

```lean
example : (1 : Nat) + 1 = 2 := by
  rfl
```

In Litex, the input is the fact itself:

```litex
1 + 1 = 2
```

Lean can also be concise. The main difference is the default interface: a common Lean workflow supplies instructions for constructing a proof, here `rfl`, while Litex asks you to state the fact that should hold and lets the checker find its grounds. The extra notation that people often find cumbersome in Lean becomes more visible in definitions, representations of object identity, and sets. Lean also permits cleaner alternative encodings; these examples compare common surface forms.

A function with a restricted domain. Litex writes the condition on the parameter:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

Here we can also see how closely a Litex statement corresponds to an ordinary-language description. We are defining a function called reciprocal (`have fn reciprocal`), whose domain consists of nonzero real numbers (`(x R: x != 0)`). For an argument x, the return value is real (`R`) and equals 1/x (` = 1/x`).

A common Lean encoding puts the condition into a subtype, so a call packages the value together with a proof:

```lean
def reciprocal (x : {y : ℝ // y ≠ 0}) : ℝ :=
  (x : ℝ)⁻¹

example : reciprocal ⟨2, by norm_num⟩ = (2 : ℝ)⁻¹ := by
  simp [reciprocal]
```

One number can accumulate several membership facts. In Litex, we can keep adding facts about the same `1`: it belongs to the integers, the reals, and the complex numbers:

```litex
1 $in Z
1 $in R
1 $in C
```

In Lean's surface language, this more often involves choosing types or inserting coercions:

```lean
example : ((1 : ℕ) : ℤ) = (1 : ℤ) := by simp
example : ((1 : ℝ) : ℂ) = (1 : ℂ) := by simp
```

Defining a set. Litex stays close to ordinary mathematical writing:

```litex
have multiples_of_four power_set(N) = {a N: a % 4 = 0}
4 $in multiples_of_four
```

Again, the statement corresponds closely to an ordinary-language description. We are defining a set called multiples_of_four (`have multiples_of_four`), declaring it to be an element of the power set of the natural numbers (`power_set(N)`), and setting it equal to `{a N: a % 4 = 0}`.

Lean explicitly specifies the carrier type and commonly uses `simp` to unfold the definition:

```lean
def multiplesOfFour : Set ℕ := {a | a % 4 = 0}

example : (4 : ℕ) ∈ multiplesOfFour := by
  simp [multiplesOfFour]
```

When you enter `1 + 1 = 2`, Litex returns:

```
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

When you enter `1 / 0 = 1 / 0`, Litex returns the following abbreviated feedback:

```
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
    },
  }
  ...
}
```

The benefit is that Litex makes explicit why a step holds, while many other formal-language workflows do not present that explanation by default. Here, for example, the output says that `1 + 1 = 2` was proved by the `Closed calculation` rule. Litex's output is available in Chinese, English, and roughly ten languages in total. Users state what they want to prove; the Litex kernel explains why it holds.

Litex's `litex -session` interactive mode resembles Python's REPL: a failed statement leaves previously accepted definitions and facts available. It is like working on a scratchpad. A mistake is harmless to the accepted context; only accepted work becomes context for later input. For example, after accepting `let a = 2`, trying `a = 3` fails, but the same session can still use `a` to verify `a + 1 = 3`. The failed step is discarded and the accepted context remains. In a common Lean file workflow, an edit often triggers another round of the relevant checks; Litex makes incremental retention of accepted facts part of its interactive experience. `litex -latex` can also turn Litex into LaTeX source for easier reading.

I think of Litex as a strict teacher beside you. If its kernel cannot prove a fact you enter, it flags the step as unjustified; when it can, it teaches you why the step holds.

This choice shaped the verification engine. In a typical Lean tactic workflow, the author gives instructions that construct a proof, which is ultimately checked by a kernel. Litex puts the next mathematical fact at the center of the interaction: given the current context, can the system justify this statement? This is a choice about the default writing experience; other proof assistants also provide declarative interfaces and automation. Lean's documentation explains its own elaboration and checking model.

Litex has more than 600 built-in rules and a layered, recursive verification process for finding appropriate proof routes. Its vocabulary includes dozens of object forms, such as numbers like `1`, functions such as `+`, and set operations such as `union`; dozens of statement forms, including definitions such as `let a = 1`; and dozens of fact forms, including inequalities such as `1 < 2`, existential facts such as `exist x R st {x > 1}`, and universal facts such as `forall a Z => a $in R`. The verifier needs enough context. If you skip too many steps, its search engine may be unable to find or derive what you want to prove.

My earliest implementation of this idea—finding relevant facts in context and applying appropriate rules to check each step—was simple: matching and substitution. Find a relevant known fact, match it against the statement being checked, and determine whether the required substitutions and conditions are valid. That idea developed into structured fact lookup, bounded recursive verification, built-in mathematical rules, and explicit statements for proof steps such as introducing witnesses or splitting into cases.

With the built-in rules in place, the task is to read the user's input and determine which rules and contextual facts can establish it. Without the required context or an applicable rule, the system cannot prove the statement. For example, `a = 1` is `unknown` when I do not know what a is. Only after you introduce `let a = 1` can Litex find the relevant context and prove a subsequent `a = 1`.

There are many common mathematical object and statement forms, but they form a finite vocabulary to work with. One contribution I see in Litex is that, through two years of exploration, I have connected familiar relationships among objects and statements so that everyday mathematical expressions can correspond almost one for one to Litex statements. Familiar objects have definitions and relationships with other objects; these connections are captured in Litex's more than 600 built-in rules. Users should not have to manage all these trivial details themselves.

But checking a statement is only part of what I want. I also want an explanation of the verification: which facts it used, which rules connected them, and where a step could not be justified. Litex therefore has a search engine specialized for mathematics, operating on a database structure specialized for mathematics. It uses the context and built-in mathematical inference rules to find and check grounds for supported statements.

Turning familiar mathematical expressions, step by step, into knowledge that a machine can recognize, store, and reuse is difficult. This is the core of the Litex project and the work performed by its kernel, with more than 200,000 lines of Rust source. I spent two years exploring what I was building while building it; AI helped me work through the engineering details. Even as a programmer who relies on hundreds of keyboard shortcuts, I could not have built a project of this size without AI. I had to develop the mathematical database and search engine for this design myself. That machinery is now implemented: the pipeline checks statements and produces results explaining why they hold. This also suggests a use in mathematics education. We can build interactive textbooks written in Litex source that resembles natural language, with each statement connected to structured information about why it holds. Linking those records creates a network through which readers can see how mathematical concepts connect. The experience could change how they think about mathematics, code, and proof.

A small age example makes this pipeline concrete. The same reasoning appears as Litex source, JSON explaining its grounds, and Lean generated by `-lean`. Compilation is currently a preview feature; the Lean column below contains excerpts from actual output.

```litex
let my_age = 3
let brother_age = 3 * my_age
brother_age = 3 * 3 = 9
```

| Litex source | JSON (verification summary) | Lean (`-lean` excerpt) |
| --- | --- | --- |
| `let my_age = 3`<br>`let brother_age = 3 * my_age`<br>`brother_age = 3 * 3 = 9` | <pre>{<br>  "statement_result": "accepted",<br>  "statement": "brother_age = (3 * 3) = 9",<br>  "proof_method": {<br>    "type": "compound_fact",<br>    "rule_name": "Chain"<br>  },<br>  "stores": [<br>    "brother_age = (3 * 3) = 9",<br>    "brother_age = (3 * 3)",<br>    "(3 * 3) = 9"<br>  ]<br>}</pre> | <pre>noncomputable def _object_i1 :=<br>  Litex.number (M := M) (3 : ℂ)<br><br>theorem h_1 :<br>  Litex.Same (_object_i1 …)<br>    (Litex.number … (3 : ℂ)) := …<br><br>-- … intermediate steps omitted …<br><br>theorem h_470 :<br>  Litex.Same (_object_i2 …)<br>    (Litex.number … (9 : ℂ)) := …</pre> |

On the left is the mathematics a person writes; in the middle is the machine's record of why it holds; on the right is the proof's form after connecting the result to Lean. An interactive textbook uses the middle column. Independent rechecking takes the next step to the right.

Once verification produces a structured record, further possibilities emerge.
The relationships between definitions and established facts can support knowledge graphs. AI agents can use the feedback to revise a failed step and continue from accepted knowledge. Building a capable mathematical agent around this interaction is one of my longer-term goals.

The same record also provides a bridge to Lean. A compiler can use both the Litex source and its verification results to generate Lean statements and proofs, following the reasoning Litex actually used. With so much source code, readers may wonder whether bugs undermine its rigor. Litex can certainly have bugs, but supported Litex proofs can be compiled to Lean for an independent check. One way to understand the layers is that Lean elaborates surface proofs into core terms in dependent type theory, whose foundations include typed lambda calculus, and its kernel checks those terms. Litex can translate supported reasoning into Lean to obtain that additional check. From this perspective, Litex can also be understood as a higher-level interface over Lean.

Litex's own checking works at the level of mathematical objects, rules, and context, rather than directly constructing low-level lambda-calculus proof terms. Its architecture separates two stages: first Litex checks the reasoning, which may be enough for the immediate exploration; then, if you want an independent check because you are concerned about bugs in Litex's verifier, supported routes can be compiled to Lean and checked there. The first stage can be fast because its architecture centers on a mathematical database and search. The following local spot check was recorded on October 21, 2026: Litex used `target/release/litex -f`, and Lean used `lake env lean` in a project with an existing Mathlib cache to check the same small examples. Lean's times are from a second, warmer run. This is not a formal benchmark; see the [Lean–Litex example comparison](Representative_Lean_Litex_Example_Comparisons.md#9-local-runtime-spot-checks) for detailed conditions and guidance on interpreting it fairly.

| Scenario | Litex (median) | Lean (2nd warmer run) | Approximate difference |
| --- | --- | --- | --- |
| Short arithmetic / `x = 2` ⇒ `x + 1 = 3`, `x^2 = 4` | ~6 ms | ~7 s | ~1000× |
| Calculation chain for two linear equations in two unknowns | ~16 ms | ~30 s | ~2000× |
| Sets: intersection preserves inclusion; `{1,2} ∈ {{}, {1,2}}` | ~4 ms | ~3.4 s | ~800× |
| Large witness `witness exist a, b, c, d N+ st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481` | ~5 ms | ~16–21 s (both `norm_num` and `native_decide` were slow) | ~3000×+ |
| Control: Lean's `1 + 1 = 2` without Mathlib | — | ~2.3 s (`lake env lean` startup alone) | Litex still takes only a few milliseconds for the whole file |

I see enormous value in compiling Litex to Lean. It gives Litex a path into the Lean ecosystem and adds an independent check on translated proofs. Many readers find Lean difficult to read, and some of its default semantics differ from ordinary mathematical expectations. Litex offers a route toward making formal tools more accessible: familiar expression and fast checking in Litex, with deeper libraries and independent kernel rechecking available through Lean. For more complete examples side by side, see the [Lean–Litex example comparison](Representative_Lean_Litex_Example_Comparisons.md); for the overall design, see the [Litex Blueprint](Litex_Blueprint.md).

Although AI is disrupting how mathematical research is evaluated, I think this is the best time to learn mathematics; 3Blue1Brown discusses this in [*There's never been a better time to go into math*](https://www.youtube.com/watch?v=LKrwhjOI8Nc). Most people do not need to conduct mathematical research. They need to use mathematics as a tool for understanding the world. To me, AI has not yet solved the problem of mathematical understanding: as a learning aid, it often feels like an electronic tutor focused on solving exercises. But AI has made it possible to build projects like Litex quickly. Litex revisits questions such as what mathematics is and what reasoning means from first principles. My hope is that, after learning Litex, readers will see mathematics written in ordinary language and think of Litex—and remember that mathematics itself is a rigorous language, with logic and connections behind it. That would be enough for me.

Litex is still under rapid development. Please try it and share your suggestions. The website is [litexlang.com](https://litexlang.com/), and the source code is available in the [golitex repository](https://github.com/litexlang/golitex). To learn more about how Litex works, contact [litexlang@outlook.com](mailto:litexlang@outlook.com).
