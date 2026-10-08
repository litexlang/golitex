# Learn Litex: from a checked fact to your own mathematical file

Write `1 + 1 = 2`, check it, and grow that same habit into a definition and a
proof. This course takes you through the decisions needed to make a small
mathematical development in Litex: what the objects are, where they are defined,
what is already known, and what still needs to be proved.

You need basic arithmetic and school algebra. No programming or proof-assistant
experience is assumed. Plan for about **90 minutes for the main course** and
**30 minutes for the optional extensions**, including time to run and change
examples. These are study estimates, not measured completion times.

By the end, you should be able to define a function with its legal inputs, state
a general property, give a short proof, interpret a failed check, and save a
self-contained `.lit` file. You will also see how this checked source can serve
a human reader or an AI agent.

## Your route

| Part | What you will make or understand | Suggested time |
| --- | --- | --- |
| [1. Check your first fact](#1-check-your-first-fact) | A mathematical sentence Litex can check | 8 min |
| [2. Give objects and properties names](#2-give-objects-and-properties-names) | A value, a function, and a property | 12 min |
| [3. Make the domain explicit](#3-make-the-domain-explicit) | A reciprocal that excludes zero | 12 min |
| [4. Move from examples to general facts](#4-move-from-examples-to-general-facts) | A universal statement and a local proof | 15 min |
| [5. Write a proof that follows the mathematics](#5-write-a-proof-that-follows-the-mathematics) | Definition unfolding, an equality chain, and cases | 13 min |
| [6. Read a failure and make a small repair](#6-read-a-failure-and-make-a-small-repair) | A corrected domain and an honest reading of feedback | 15 min |
| [7. Finish your first lit file](#7-finish-your-first-lit-file) | A complete checked artifact and a next step | 15 min |
| [Optional extensions](#optional-extensions) | Named results, existence, and an agent loop | 30 min |

Read the main course in order. For each example, first predict what it means,
then run it, and finally try the suggested change. If you are reading on GitHub
or in a downloaded Markdown file, all the explanations and code are here;
the course does not depend on a particular page interface.

Each `litex` code block is a complete independent example. Start a fresh
playground run for each block, or save it in its own `.lit` file. Blocks marked
`text` show an intentional failure, a fragment, or a transcript; their captions
explain which. Do not paste them into a passing file without making the repair.

## Choose where to run examples

On the website, use the editor beside a Litex example when one is available,
or copy the whole block into the [online playground](https://litexlang.com).
Edit the source and run the check. You do not need to install anything to read
the course or try these small examples online.

For local use, follow the [setup guide](setup.md), then check your installation:

```bash
litex -version
litex -strict -e '1 + 1 = 2'
```

To check a saved file in English:

```bash
litex -lang en -strict -f first.lit
```

For these exercises, keep files in a new directory without a `litex.config` so
each file runs on its own. We introduce project context in an optional extension.
The [CLI reference](cli.md) explains installation-independent command details.

## 1. Check your first fact

**Question:** Is $2(3+4)=14$? How can you record the calculation so someone else
can check the same sentence?

```litex
1 + 1 = 2
2 * (3 + 4) = 14
3^2 = 9
```

These lines are **facts to check**. They do not ask Litex to search for an answer
or print the value of an expression. You supply a mathematical sentence, such
as `3^2 = 9`, and Litex checks it with its available rules and context.

`*` means multiplication and `^` means exponentiation. `=` states mathematical
equality. It is not a command that assigns a new value to the left-hand side.
Write multiplication explicitly: use `2 * x` rather than `2x`.

A successful batch check has `"success": true` and `"session_error": null` in
its JSON result. The website may present that result more simply. The
interactive command-line REPL prints `success` for a successful input block.
We will read a failed result more carefully in Part 6.

**Try:** Change the second line to `2 * (3 + 5) = 16`. Predict the result before
running it. Then deliberately change the right-hand side to `15`.

The first change should pass; the second should fail. For this particular
calculation, ordinary arithmetic also tells you the changed equality is false.
A failed Litex check in general needs more interpretation than that.

**Take away:** A Litex file records mathematical statements that can be checked.
Your first task is to say precisely what you want checked.

## 2. Give objects and properties names

The next step is to say what your symbols mean. A name for a number, a callable
function, and a property have different jobs.

### A name for a specific value

**Question:** If a real number `x` is 2, can we check a calculation using that
name?

```litex
have x R = 2
x + 1 = 3
x^2 = 4
```

`have x R = 2` introduces `x`, checks that its value belongs to `R`, and makes
`x = 2` available. `R` is the set of real numbers. Later facts can use this
checked information.

The same symbol continues to denote the same mathematical object. This course
does not use mutable variables: writing `x = 3` next would request an equality
inconsistent with the value already chosen.

Compare a name whose value has **not** been chosen:

```litex
have x R
x + 0 = x
x $in R
```

Here `x` is an arbitrary real number. Its membership in `R` is known; `x = 2`
is not. The identity `x + 0 = x` works for that arbitrary real number.

### A function with a defining equation

**Question:** What is the distance of a real number from zero?

The mathematical definition is $d(x)=|x|$:

```litex
have fn distance_from_zero(x R) R = abs(x)
distance_from_zero(-3) = distance_from_zero(3) = 3
```

Read the first line as: “define a function named `distance_from_zero`, with
real input `x`, real output, and value `abs(x)`.” `abs` is absolute value.
The name can now be applied to an input, as in `distance_from_zero(-3)`.

The second line is an equality chain. It asks for both adjacent equalities:
the distance at `-3` equals the distance at `3`, and that distance equals `3`.
Function definitions describe mathematical values; they do not by themselves
promise that an exporter can turn every definition into a Python program.

### A property with a meaning

**Question:** How do we name “this real number is above two”?

```litex
prop is_above_two(t R):
    t > 2

by def $is_above_two(3)
```

`prop` introduces a named property. Its indented body gives the meaning:
`is_above_two(t)` means `t > 2`. The `$` marks a property application in a fact.

Declaring a property does not prove it for every input. `by def
$is_above_two(3)` checks the defining condition at `3` and folds it into the
named property. At `1`, the condition would not hold.

| What you need | Form used here | What it contributes |
| --- | --- | --- |
| A named value | `have x R = 2` | A name, membership, and a value equation |
| An arbitrary real object | `have x R` | A name and membership, with no chosen value |
| A function | `have fn f(x R) R = ...` | A callable value with a defining equation |
| A property | `prop P(x R): ...` | A name for a mathematical condition |
| An instance of a property | `by def $P(value)` | A checked use of that definition |

**Try:** Change both `3` inputs in the distance example to `5` and adjust the
last value. Then change the input of `is_above_two` from `3` to `1`.

**Take away:** Objects are what you talk about. Facts say something about those
objects. Definitions make their meaning available for later checks.

## 3. Make the domain explicit

Before asking whether a fact holds, check whether its expressions have a
meaning for the inputs you allow.

### Sets and membership

```litex
0 $in N
-2 $in Z
1 / 2 $in R
2 $in {1, 2, 3}
```

`N` is the set of natural numbers, including zero; `Z` is the set of integers;
`R` is the set of real numbers. `$in` means “belongs to.” Braces such as
`{1, 2, 3}` describe a displayed finite set.

The same object can belong to several sets: `2` is natural, integer, and real.
When you write `have x R` or `forall x R`, you introduce a mathematical object
with membership in `R`. You do not convert it into a programming-language
floating-point value. Litex's [object model](Manual.md#pure-set-object-model)
uses sets as its foundation; this membership-based reading is enough for the
examples in this course.

### The reciprocal needs a legal input

**Question:** Define the reciprocal of a real number, then prove that multiplying
it by the original number gives one. Which inputs are allowed?

The intended definition is $r(x)=1/x$ for $x\ne0$. Put that restriction in the
function itself:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
reciprocal(-4) = -1 / 4
```

Inside the input parentheses, `x R` gives the set and `: x != 0` gives an
additional input condition. The `R` after the parentheses gives the output
set. Litex checks the body `1 / x` for every legal input.

This is an important part of a mathematical interface. Every later call to
`reciprocal` must supply a real, nonzero argument. The restriction belongs to
the definition, so callers can see it without searching through a later proof.

Here is an **intentional failing definition**; this is not a runnable example
to keep in your finished file:

```text
have fn reciprocal(x R) R = 1 / x
```

It admits zero even though the body divides by `x`. The first repair is to
restore the nonzero input condition. A longer proof of a later property cannot
make division by zero meaningful.

**Try:** In the passing block, change the last line to `reciprocal(0) = 0`.
Expect a failure at the function's input condition. Then restore a legal input.

**Take away:** A domain is part of the mathematics. A rejected function call
may be a problem with the expression's meaning before any proof is attempted.

## 4. Move from examples to general facts

Checking values at `2` and `-4` does not prove a law for every nonzero real
number. Use quantification to state the actual scope of your claim.

### For every input

**Question:** Does doubling a real number agree with adding it to itself?

```litex
have fn double(x R) R = 2 * x

forall x R:
    double(x) = x + x
```

Read `forall x R:` as “for every real number `x`.” Its indented body states the
facts to be checked. The binder `x` inside the universal statement is local;
it is not a new global number with a chosen value.

The function's own parameter and the universal statement's parameter happen
to have the same spelling. Their scopes are separate. Indentation tells you
which body belongs to which header.

### If a condition holds

**Question:** What follows if a real number is positive?

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

Facts above `=>:` are **hypotheses**. Facts below it are **conclusions**. This
statement says: for every real `x`, **if** `x > 0`, **then** `x != 0`.

The hypothesis is local to this implication. It does not claim that every real
number is positive, and it does not make an unrelated global `x > 0` available.
Without hypotheses, write the conclusion directly under `forall`, as in the
doubling example.

### When you want to show the route

An ordinary universal fact can pass directly when the verifier already has
the necessary rules. When you want to provide proof steps, introduce a `claim`.

**Question:** I am 8 years old. My brother is 5 years older. My mother's age is
three times my brother's age minus 2. What is my mother's age?

The proof idea is to calculate the brother's age first: $8+5=13$. Then the
mother's age is $3\cdot13-2=37$.

```litex
claim:
    ? forall my_age, brother_age, mother_age Z:
        my_age = 8
        brother_age = my_age + 5
        mother_age = 3 * brother_age - 2
        =>:
            mother_age = 37
    brother_age = my_age + 5 = 13
    mother_age = 3 * brother_age - 2 = 37
```

`?` marks the **goal** of this proof block. Here the goal is the whole
conditional universal statement. In the proof body, its parameters and
hypotheses are available, so the two calculation lines can use them.

The final line is checked against those hypotheses and earlier steps. The
goal is not accepted merely because you wrote it after `?`. After a successful
claim, the completed goal becomes available outside the block; its local
parameter names do not.

A bare `forall` body contains facts. Proof commands such as `by def` and
`by cases` belong inside a proof body such as a `claim`. This separates what
you are asserting from the route you give to establish it.

**Try:** Change `my_age = 8` to `my_age = 9`. Work out both new ages on paper,
then update the intermediate value and the goal together. Leaving the old
conclusion `37` should not pass.

**Take away:** `forall` states the scope, `=>:` states the assumptions, and
`claim` gives you a place to write the derivation.

## 5. Write a proof that follows the mathematics

A good first proof starts with the mathematical move. For the reciprocal,
substitute its defining equation and cancel the nonzero factor.

### Define, unfold, calculate

**Question:** Prove $r(x)x=1$ whenever $x$ is a nonzero real number.

```litex
have fn reciprocal(x R: x != 0) R = 1 / x

claim:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1
```

There are three pieces of meaning to keep together:

1. The definition restricts `reciprocal` to nonzero real inputs.
2. The goal restricts the multiplication law to those same inputs.
3. The proof exposes the defining equation and follows it with the equality
   chain that establishes the law.

The line `reciprocal(x) = 1 / x` makes the useful equation explicit before it
is used inside multiplication. The last equality uses `x != 0`. The proof
follows the familiar mathematical argument rather than a search through a
list of tactic names.

### Prove a named property

**Question:** Show that every distance from zero is nonnegative.

```litex
have fn distance_from_zero(x R) R = abs(x)

prop is_nonnegative(t R):
    t >= 0

claim:
    ? forall x R:
        $is_nonnegative(distance_from_zero(x))
    distance_from_zero(x) = abs(x) >= 0
    by def $is_nonnegative(distance_from_zero(x))
```

The calculation establishes the numerical condition. `by def` then checks
that this condition supplies the meaning of the named property. A function
definition and a property definition have different roles: the first supplies
a value, and the second describes that value.

### A proof by cases

**Question:** Set negative inputs to zero and leave other inputs unchanged.
Does this operation always return a nonnegative number?

For a real input, either `x < 0` or `x >= 0`. In the first case the output is
zero; in the second it is the input itself:

```litex
have fn clamp_at_zero(x R) R by cases:
    case x < 0: 0
    case x >= 0: x

claim:
    ? forall x R:
        clamp_at_zero(x) >= 0
    by cases:
        ? clamp_at_zero(x) >= 0
        case x < 0:
            clamp_at_zero(x) = 0
            0 >= 0
        case x >= 0:
            clamp_at_zero(x) = x
            x >= 0
```

The definition chooses a value in each case. The proof checks the same goal
in each branch. The branches must cover the possibilities; choosing two
convenient examples would not establish the universal result.

Some simple conclusions in these examples can already be inferred. We keep
the defining equations and concrete branch conclusions visible because they
explain the mathematical move. You do not need to expand every routine
arithmetic or membership consequence into a separate proof.

**Try:** Check `clamp_at_zero(-2) = 0` and `clamp_at_zero(2) = 2` by appending
them to the complete block. Then try changing the negative branch to `-1`.
Predict which part of the universal proof will fail.

**Take away:** Write the mathematical steps you need: unfold a definition,
give a useful intermediate equation, or split exhaustive cases. Each step
still has to be checked in its actual context.

## 6. Read a failure and make a small repair

A failed check asks you to inspect the source and the first failing stage.
It is not automatically a proof that your mathematical goal is false.

### Failure A: an expression is outside its domain

This **intentional failing block** defines a legal reciprocal but asks for a
law over too large a domain:

```text
have fn reciprocal(x R: x != 0) R = 1 / x

claim:
    ? forall x R:
        reciprocal(x) * x = 1
```

`x` is an arbitrary real number here. Nothing excludes zero, so the goal
contains a function application whose input condition is missing. Repair the
goal before trying to extend its proof:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x

claim:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1
```

This restores the statement we intended from the start: the product law for
nonzero real inputs. We have not proved a law at zero or changed the function
to admit an input where its equation has no meaning.

### Failure B: the context does not establish the fact

This is another **intentional failing block**:

```text
have x R
x != 0
```

The expression is meaningful, but an arbitrary real number need not be
nonzero. Decide which mathematics you intended. If `x` was meant to be the
specific value `2`, introduce that value:

```litex
have x R = 2
x != 0
```

If you intended a conditional law about arbitrary nonzero numbers, write the
condition as a hypothesis, as in the reciprocal proof. If the target really
should follow from existing facts, give the missing intermediate fact or use
an established result. Adding an assumption without a mathematical reason
changes the problem.

### Read the result at the right level

Local batch commands such as `litex -lang en -strict -f first.lit` return JSON.
Check the overall `success`, then inspect failed entries in
`statement_results`. `session_error` reports a hard error; it is normally null
for an ordinary verification failure. A failed batch exits with a nonzero
status. For a successful batch, require both exit status zero and a successful
JSON result.

The following is a **selected-field excerpt** of the successful file result;
other fields, including the statement results, are omitted:

```json
{
  "kind": "run",
  "success": true,
  "target": "file",
  "session_error": null
}
```

For Failure A, the failed claim's feedback identifies the goal's
well-definedness check. “Well-definedness” here means the concrete question
whether `reciprocal(x)` has a legal input. This is different from checking the
subsequent cancellation proof. A **selected-field excerpt of its failed
`statement_results` entry** is:

```json
{
  "success": false,
  "why_failed": {
    "phase": "claim",
    "failure": {
      "phase": "goal_wd"
    }
  }
}
```

The full result also includes the source and a nested failure for the unmet
`x != 0` requirement. Read the actual statement and explanation together;
detailed field names can change with versions. The
[JSON contract](cli.md#json-output-contract) is the reference for machine use.

| First problem you see | First thing to inspect |
| --- | --- |
| Parsing or indentation | The exact source shape and which body is indented |
| Unknown name | Its declaration, spelling, and scope |
| Illegal argument or division | Membership and domain conditions, especially nonzero divisors |
| A goal remains unproved | Available hypotheses, definitions, and the next small derivation |
| A later fact fails after an earlier success | What the successful statement actually made available |

Litex has built-in checking and inference for many routine facts, but it is
not a complete automatic solver for every true statement. A failure can expose
a missing proof step, unsupported automation, or a language or library gap.
For example, you can independently show a false equality is false; you cannot
infer the negation of any proposition merely because Litex failed to prove it.

### Keep accepted work during interactive repair

For local experiments, start `litex` in your exercise directory. Submit one
top-level statement at a time; end an indented block with a blank line.
This **illustrative transcript** abbreviates the failure output:

```text
litex> have x R = 2
success
litex> x = 3
[failed verification JSON]
litex> x + 1 = 3
success
```

After a normal failure that returns to the prompt, the accepted declaration
still exists. Repair the failed statement in that same session. A compound
`claim` is one statement; a pasted collection of separate statements can
contain earlier successes even if a later statement fails.

If the process stops, or you deliberately need to replace a definition already
accepted under the same name, start a fresh session and replay your accepted
source. A saved file checked from a clean process is the final evidence;
an interactive result alone can depend on earlier input you forgot to save.

### Know what a successful check assumes

The examples in this course use no user `trust` or `axiom` statements.
`-strict` rejects those statements, including inside proofs or dependencies.
It still relies on Litex's implementation, built-in rules, and permitted
foundational interfaces. It is not an independent proof of the checker itself.

You may encounter `trust` in other material. It explicitly accepts a fact
without completing its proof. Using it to make an exercise green leaves a
proof obligation; it does not teach you how to prove that exercise. Read the
[trust boundary](Manual.md#trust-and-strict-mode) when you need this feature.

**Try:** Run Failure A, find the failed claim, and repair its domain. Then run
Failure B and explain why its issue is different. Finish by checking the
repaired whole file in a fresh process.

**Take away:** Diagnose the first failed obligation, change the smallest
relevant part, and check the complete saved source again.

## 7. Finish your first lit file

You now have enough to make a small mathematical file that another reader or
agent can reproduce.

**Your project:** Define a reciprocal on nonzero reals. Prove its product law.
Check a concrete use. Also define distance from zero and prove it is
nonnegative.

First write the mathematical plan in your own words:

- The reciprocal is `1 / x`; its input must be real and nonzero.
- Substitute that equation and cancel the nonzero factor to prove the product
  law.
- Distance from zero is absolute value, which is nonnegative.

Save the following complete source as `first.lit`. Comments start with `#`:

```litex
# Reciprocal of a nonzero real number.
have fn reciprocal(x R: x != 0) R = 1 / x

claim:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1

reciprocal(2) * 2 = 1
reciprocal(2) * 4 = (reciprocal(2) * 2) * 2 = 2

# Distance from zero and a property of its output.
have fn distance_from_zero(x R) R = abs(x)

prop is_nonnegative(t R):
    t >= 0

claim:
    ? forall x R:
        $is_nonnegative(distance_from_zero(x))
    distance_from_zero(x) = abs(x) >= 0
    by def $is_nonnegative(distance_from_zero(x))

distance_from_zero(-3) = 3
by def $is_nonnegative(distance_from_zero(-3))
```

Check the saved file:

```bash
litex -lang en -strict -f first.lit
```

Keep the source and the result together when sharing it. A useful result says
which file and checker version you ran, whether the whole run succeeded, and
whether any assumptions or proof debts were added. It does not merely show
one successful line from a longer failing file.

### What makes this recognizably Litex?

The checked file exposes the objects, their meanings, and facts that later
statements consume. You can read `reciprocal(x) = 1 / x` as the same
mathematical step you would put on paper. The checker handles supported routine
consequences; you provide the domain and the useful derivation when needed.

This is a fact-oriented proof interface. In this file, that means the first
claim establishes a product law and a later calculation can use it. It does
not mean every mathematical sentence can be checked without a proof or that
Litex has the same coverage as another proof assistant.

### Why this can be math for AI

An AI model can propose the definition, goal, and proof steps you just wrote.
Litex provides a mathematical interface for checking those proposals: an
explicit input condition, statements that leave usable context, and feedback
that can point to the next repair. The `.lit` file records the accepted
development in a form that a subsequent agent can read and run again.

The emphasis is on giving AI a way to construct and revise checked
mathematical knowledge. The reciprocal example demonstrates the interface;
it does not establish that an agent will always solve a problem or that this
workflow outperforms other systems. The human still owns the intended
definition, domain, assumptions, and final mathematical statement.

### What can come after a checked file?

| Route | What it is for | Boundary to keep visible |
| --- | --- | --- |
| Python or C extraction | Executable numeric fragments | Experimental supported subset; an arbitrary `have fn` is not automatically an executable program. Source proofs do not establish floating-point accuracy. |
| Graph views | Inspecting relationships between statements and their evidence | Depends on the graph tooling and the evidence it exposes; a drawn edge is not an additional proof. |
| LaTeX rendering | Reading and presenting the mathematics | Rendering can work from parsed source; attractive output by itself does not mean the source verified. |
| Lean output | Replaying supported checked reasoning into another proof language | Preview subset; generated output must pass its own Lean check, and a native mathematical statement may need an adapter. |

Keep verification and export as separate steps. Read the current
[CLI reference](cli.md#commands),
[Lean boundary](cli.md#lean-compiler-boundary), and
[LaTeX guide](cli.md#latex-conversion-preview) before choosing an
export route. These links describe current interfaces; this course's final
file is a checked mathematical artifact, not a promise that every route
accepts all its statements.

### Check your understanding

Without copying the explanations above, answer these questions:

1. What information does `have x R = 2` add that `have x R` does not?
2. Why does the reciprocal's signature include `x != 0`?
3. What is the difference between a `prop` declaration and a proved instance?
4. Which lines are the hypotheses, goal, and proof in your reciprocal claim?
5. Why can a failed check mean something other than a false statement?
6. Why run the final file from a fresh process?

Then change the concrete reciprocal input from `2` to `5` and check an
appropriate product. Add a distance example of your own. If you can explain
the domains and repair a deliberate failure, you have completed the core
course. You do not need to memorize the entire syntax reference.

## Optional extensions

Choose these after the core course. They add tools for reuse and construction
without changing the basic habit of stating and checking facts.

### A. Name and reuse a theorem — 15 minutes

The anonymous `claim` in your first file was enough to establish its fact.
A named `thm` is useful when you want a stable result that callers can cite.

```litex
have fn reciprocal(x R: x != 0) R = 1 / x

thm reciprocal_product:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1

by thm reciprocal_product(2) => reciprocal(2) * 2 = 1
reciprocal(2) * 4 = (reciprocal(2) * 2) * 2 = 2
```

The theorem declaration checks its proof. The selected call checks the input
and hypothesis, then publishes the indicated atomic conclusion. Use
`release thm reciprocal_product(2)` when you want an unselected call that
publishes all of a theorem's conclusions. Here we select the one fact we use.
Naming every simple arithmetic identity would add ceremony; name a result
when its mathematical role or reuse makes the name helpful.

**Try:** Change the theorem call to a legal input `5` and adjust the subsequent
calculation. Then try a call at zero: the theorem's hypotheses still matter.
Replace your final file's reciprocal `claim` with this named theorem and make
one selected call before a calculation that consumes its conclusion.

Explain what you gained from the name: a specific reusable result and an
explicit citation point. Compare it with the earlier anonymous claim, whose
checked fact was already available to subsequent statements in the same file.
The name improves the interface; it does not make an unchecked statement true.

Keep your first development in one complete file. When a larger project needs
separate files and dependencies, follow the
[project organization reference](Manual.md#project-organization) and verify
both the producer and its real caller. A successful standalone proof is not
by itself evidence that every exported interface works in another module.

### B. Prove existence by giving a witness — 10 minutes

**Question:** Is there a real number whose square is four?

Give a witness that satisfies the condition:

```litex
witness exist w R st {w^2 = 4} from 2
obtain root from exist w R st {w^2 = 4}
root^2 = 4
```

`exist w R st {...}` means “there exists a real `w` such that the facts in
braces hold.” `witness ... from 2` supplies `2` and checks the condition after
substitution. `obtain` extracts a fresh name `root` from a checked existence
fact; it does not guess a root of an arbitrary equation.

The name `w` is local to the existence statement. The extracted `root` belongs
to the surrounding scope. Its square is known to be four; this does not tell
you that `root` must be the positive root.

For a witness that depends on a universally quantified input, construct it
inside the active input's scope:

```litex
claim:
    ? forall x R:
        exist y R st {y = x + 1}
    witness exist y R st {y = x + 1} from x + 1
```

Read the mathematical move first: for a given real `x`, choose `x + 1`.
The claim exports the universal existence statement, not a global `x` or `y`.

`exist!` additionally requires uniqueness. The square-four problem has both
`2` and `-2`, so one witness is not a proof of unique existence. A genuinely
unique specification is:

```litex
witness exist! w R st {w = 2} from 2
```

**Try:** Use `-2` as the square-four witness. Explain why this passes while
claiming a unique square-four root would fail.

### C. Use the same course with an AI agent — 5 minutes

Give the agent a mathematical problem, the relevant definitions, and the
current checked source. Ask for the natural-language proof idea before code.
A useful request for this course is:

```text
Define reciprocal on nonzero real inputs in Litex.
Prove reciprocal(x) * x = 1 under that input condition.
Explain the proof idea, then return a complete standalone .lit file.
Use no trust or axiom. Keep the domain and conclusion unchanged.
Run the checker; if it fails, show the first failed obligation and the
smallest repair. Finish with a clean whole-file check and its result.
```

The loop is the one you have practiced: propose a statement or proof step,
check it, read the feedback, repair it, and retain accepted work. Normal
interactive failures need not erase earlier successes. Save the source so a
fresh process can reproduce the complete result.

The checker does not decide whether the agent formalized the problem you
actually meant. Review the definition, domain, hypotheses, and conclusion
before treating a successful run as an answer to the original question. For
longer agent sessions and replay discipline, use the [Agent Guide](AgentGuide.md).

## Answers to the core checkpoints

1. `have x R = 2` adds a specific value equation; `have x R` only introduces
   an arbitrary real object and its membership.
2. The reciprocal divides by its input. Zero must be excluded in the
   definition, and a theorem using it must satisfy that same condition.
3. `prop` gives a meaning. A proved instance establishes that the defining
   conditions hold at particular arguments.
4. In the reciprocal claim, `x != 0` is the hypothesis; the statement after
   `?` is the whole goal; the two equalities below it are the proof body.
5. A failure may concern parsing, names, domains, missing proof steps, or a
   checking limitation. It does not establish a proposition's negation.
6. A fresh file run checks that all the needed context was saved and that no
   forgotten interactive input is supplying the proof.

For the age exercise with `my_age = 9`, the brother is `14` and the mother is
`40`. For the clamp exercise, a negative branch returning `-1` cannot prove a
nonnegative-output law. For the reciprocal at `5`, a suitable fact is
`reciprocal(5) * 5 = 1`.

## Continue from the thing you want to do

| Your next task | Read next |
| --- | --- |
| Find the right declaration or proof action | [Learner Cheatsheet](Litex_Learner_Cheatsheet.md) |
| Look up precise syntax, semantics, or a proof pattern | [Manual](Manual.md) |
| Install Litex or understand CLI feedback | [Setup](setup.md) and [CLI](cli.md) |
| Understand the language's research direction | [Litex Blueprint](Litex_Blueprint.md) |
| Build a reproducible agent workflow | [Agent Guide](AgentGuide.md) |

For your next file, choose one small problem you can solve on paper. Write its
objects and legal inputs first, state exactly what you want to prove, and grow
the checked source one useful mathematical step at a time.

The 20 independent Litex examples in this guide were checked on 2026-10-08
with a current-source release build of Litex 1.0.0-beta, using English output
and strict mode. Expected failures are labeled separately. Litex is evolving;
when an example behaves differently, keep its complete source and checker
version with the feedback.
