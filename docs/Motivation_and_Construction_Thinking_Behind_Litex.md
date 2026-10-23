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

Can we find a syntax that directly connects the objects, conditions, and reasoning steps of ordinary mathematical language with expressions in a formal language? Can we find an execution model that not only checks what we write and clearly tells us why each statement holds, but also makes us think: oh, this is how I think when I do a mathematical proof. The way this language does proofs is pretty close to what goes on in my head.

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

When you enter `1 + 1 = 2` and select English output with `-lang en`, Litex returns a result for that statement. The following excerpt shows the fields relevant to its explanation:

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

When you enter `1 / 0 = 1 / 0`, the result identifies an unmet well-definedness condition. The reason appears in `errors`. Again, this is an excerpt of the relevant English output:

```json
{
  "run_result": "failure",
  "statement_results": [
    {
      "statement_result": "rejected",
      "statement": "(1 / 0) = (1 / 0)"
    }
  ],
  "errors": [
    {
      "statement_index": 0,
      "statement": "(1 / 0) = (1 / 0)",
      "phase": "well_defined",
      "message": "Could not prove that the statement is well-defined.",
      "category": "well_defined",
      "expression": "(1 / 0)",
      "obligation": "0 != 0"
    }
  ]
}
```

The same process applies to the reciprocal function above. To check `reciprocal(2) = 1 / 2`, the argument must satisfy `2 != 0` before the function definition can be used to check the equality. Replacing it with `reciprocal(0)` leaves the required nonzero condition unmet. Checking an existential witness requires confirming that it belongs to the specified set and satisfies the stated properties. Checking `by def $is_above_two(3)` requires establishing the defining condition `3 > 2`.

I want the system to display these mathematical grounds directly. The output above explains that `1 + 1 = 2` was checked by the `Closed calculation` rule, while the division-by-zero example identifies the condition that cannot be met. Litex provides output in ten languages, including Chinese and English; fixed values such as `accepted` and `rejected` remain English. Users write mathematical objects and steps; the checker returns the grounds it found, or identifies the conditions and proof evidence still missing. Structured verification records also need a presentation suited to their readers before they become clear teaching explanations.

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

| Litex source | JSON (English verification summary) | Lean (`-lean` excerpt) |
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

Although AI is disrupting how mathematical research is evaluated, I think this is the best time to learn mathematics; 3Blue1Brown discusses this in [*There's never been a better time to go into math*](https://www.youtube.com/watch?v=LKrwhjOI8Nc). Most people do not need to conduct mathematical research. They need to use mathematics as a tool for understanding the world. To me, AI has not yet solved the problem of mathematical understanding: as a learning aid, it often feels like an electronic tutor focused on solving exercises. Litex takes a different approach. It revisits questions such as what mathematics is and what reasoning means from first principles. My hope is that, after learning Litex, readers will see mathematics written in ordinary language and think of Litex, and remember that mathematics itself is a rigorous language, with logic and connections behind it. That would be enough for me.

Litex is still under rapid development. Please try it and share your suggestions. To learn more about how Litex works, contact [litexlang@outlook.com](mailto:litexlang@outlook.com).

Appendix:

## Comparing Litex and Lean in Design and Implementation

**1. Lean puts mathematical objects, propositions to be proved, and proofs into the same type-theoretic framework. Propositions are types, and proofs are terms of those types. This makes the language powerful and general, but it can also be confusing for learners. Litex keeps objects and facts separate.**

For example, in Lean:

```text
a : ℝ       a is a real number
P : Prop    P is a proposition
h : P       h is a proof of P
```

Objects, propositions, and proofs are all expressed in this form: something has a type.

In Litex:

```litex
have a R = 2
a + 1 = 3
```

The first statement introduces an object. The second states a fact about that object. Objects are objects, and facts are facts.

`a + 1` is an object expression. It has not said that anything holds yet. On its own, it cannot be submitted as a fact to check in Litex, because it makes no assertion.

`a + 1 = 3` is a fact expression. It says something that needs to be checked.

**2. Proofs in Litex source mostly go from the bottom up: start from the assumptions, build up intermediate steps, and finally reach the result. Each statement may depend closely on the one just before it, or it may use something much earlier. So reading Litex is like reading a textbook from the first page to the last. Lean's common goal-driven style feels more like going from the top down: start with the result and keep changing what still needs to be proved. When reading it, you have to follow those changes in the goal. Reading this kind of Lean proof can feel a bit like reading a textbook from the last page back to the first.**

This does not mean Lean can only work from the top down. Lean also has `have` and `calc`, so you can write forwards from the assumptions. I am talking about how these two styles feel to read.

For example, suppose we know:

```text
P
P implies Q
Q implies R
```

Starting from the assumptions:

```text
P holds, so Q holds, so R holds.
```

Starting from the goal:

```text
To prove R, it is enough to prove Q.
To prove Q, it is enough to prove P.
P is already known. Done.
```

Here is a calculation example:

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = (-4)
```

First eliminate a variable to get `y`, then substitute back to get `x`. The last statement uses both the previous result and the original assumptions. You can read straight through the mathematics as it happens.

3. **If people cannot correctly and intuitively understand the mathematics they are stating, or the corresponding formal code, then as AI starts introducing mathematical concepts of its own and proving theorems about them, semantic drift in Lean formalizations could become a systemic pitfall that is even harder to spot than memory leaks in C.**

4. **In its implementation, Lean often uses layers of types, structures, and type classes to express mathematical concepts. Litex takes a different route. It directly provides a collection of common mathematical concepts and statements, with built-in relationships and properties, and users continue doing mathematics on top of these.**

Litex does more than clearly show the mathematical objects in your code. It also shows the mechanism behind your proof. You should feel that the objects Litex works with are the mathematical objects you know, and the way it does proofs is the way you know how to do proofs. For each statement asserting a fact, if Litex cannot find a proof, it remains unproved, or "unknown" in this sense. An ordinary failed statement does not stop the later proof steps. If Litex finds the context and proof rules that justify it, the fact is accepted as true and stored as part of the context for later steps.

The difference between context and proof rules:

```litex
let a = 2
a + 1 = 3
```

Here, `a = 2` is part of the context for `a + 1 = 3`; substituting the value of `a` and checking that `2 + 1` really equals `3` is the proof rule. The context comes from your Litex source: the definitions, assumptions, and facts available at that point. The rules are built into Litex. Litex has hundreds of common rules to make things easier for users. Each rule feels familiar on its own, but finding them, implementing them, and making them work together is a lot of work. That is also part of the hard work behind Litex.

For a Lean comparison, suppose the context already contains `h : a = 2` and the goal is `a + 1 = 3`. The closest proof is:

```lean
subst a
norm_num
```

or:

```lean
rw [h]
norm_num
```

Here `subst` / `rw` performs the substitution and `norm_num` checks that both sides are equal. The important difference is that in Lean you usually identify which hypothesis `h` to use and which tactic to apply. A Litex built-in rule instead searches the current context, finds the relevant equality `a = 2`, selects the “equality rewrite + closed calculation” route, and accepts `a + 1 = 3`. So Litex provides both built-in rules and a context-search layer that finds the right premise `h`. The author writes the fact to establish; the system finds the contextual fact that lets it pass.

One of Turing Award winner Dijkstra's important contributions was helping establish [structured programming](https://www.cs.utexas.edu/~EWD/transcriptions/EWD02xx/EWD249/EWD249.html). Basic structures such as sequences, branches, and loops let people understand a program without following a tangle of jumps. They are general enough to be useful and straightforward enough for people to connect the code with what they want to say.

Python can also be understood from this angle. Users do not have to handle [memory allocation and release for objects](https://docs.python.org/3/c-api/memory.html) themselves, and many low-level details are taken care of for them. That work still has to be done; Python's implementation does it. The more Python does for users, the more work it has to handle internally.

Litex is doing something similar: finding common patterns of expression and reasoning in mathematical language, organizing them into built-in `obj`, `fact`, and `stmt` forms, and turning common proof steps and their combinations into hundreds of built-in rules. (For Lean users, you can think of this as taking hundreds of common tactic combinations, turning them into built-in rules, and adding a database and retrieval system specialized for mathematics. Each time you enter a fact, the system looks for applicable built-in rules and the relevant context to try to prove it.) Users can write simpler proofs, but the work still has to happen inside the system. The more Litex does for users, the more its kernel has to implement, check, and maintain.

So, while so much AI work chases advanced mathematics and uses hard mathematical problems as benchmarks, Litex goes back and rethinks the basics of mathematics.
