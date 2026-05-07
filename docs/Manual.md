# Manual

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Manual

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual.md

## Manual Introduction

_In science, you can say things that seem crazy, but in the long run, they can turn out to be right. We can get really good evidence, and in the end, the community will come around._

_- Jeff Hinton_

> **Beta notice:** Litex is still in beta. The language and manual are part of an ongoing experiment in formalizing everyday mathematical reasoning. Please do not use Litex for production or mission-critical proof work yet, but we welcome attention, feedback, and discussion about the mathematical philosophy behind it.

This manual explains how Litex reads and checks mathematical proof scripts. The main idea is simple: a piece of Litex code introduces mathematical objects, states facts about them, checks those facts, and stores the successful facts for later use.

Litex has many builtin concepts because ordinary mathematics has many small background steps. Numbers, sets, membership, equality, functions, tuples, products, order, finite displays, and positivity facts constantly interact. Litex puts this shared background into the language so user proofs can focus on the mathematical idea instead of repeating basic bookkeeping.

This is the main usability advantage of Litex: proof code can stay close to the way a person would write the argument on paper. For example, using a known value can be written as direct algebraic steps:

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib.Tactic

example (x : ℝ) (h : x = 2) : x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩</code></pre>
    </td>
  </tr>
</table>

Litex's checker is designed to remember known facts, use builtin arithmetic and substitution, and infer routine consequences automatically. The result is usually shorter code, fewer proof-engine details, and a lower learning burden for everyday mathematical proofs.

> Litex is different from Lean in design goals and surface style, but its author deeply respects Lean. If you are interested in how the two languages differ in foundations, examples, strengths, and tradeoffs, see [Litex vs Lean](https://litexlang.com/doc/Litex_vs_Lean).

> You can also use this file directly as an AI agent `SKILL.md`: it is organized as a practical reference from concepts to verification flow.

---

### Mental model

When learning Litex, it is enough to keep the following mental model in mind. Try to connect each Litex idea with its everyday mathematical counterpart: the objects you write, the facts you claim, the statements that organize the proof, and the checker steps that justify and store those facts.

- **Objects** are the mathematical things a proof talks about: numbers, sets, tuples, functions, products, sequences, matrices, and names introduced earlier.
- **Facts** are judgments about objects: `x = 2`, `x $in N`, `0 <= x`, `$is_set(A)`, or a user-defined predicate such as `$prime(n)`.
- **Statements** are the user-facing forms that introduce objects, define concepts, organize local proofs, and assert facts.
- **Verification** proves the current goal from the context, definitions, evaluation, normalization, and builtin verification rules.
- **Execution** is what a statement does to the current context. A statement may define a name, open a proof block, verify a fact, store accepted facts, or run inference. Inference is one part of execution for factual statements: after a fact is accepted, Litex may add standard consequences or side information to the context.

The key distinction is that an expression such as `x + 1` is only an object. It becomes a fact only when a relation or predicate makes a claim about it, such as `x + 1 = 3`.

Many uncommon forms can be skipped at first. Read them when a proof needs them; the common core above is enough for most early examples.

---

### First reading path

If you are reading the manual to understand how Litex works, start with the things Litex handles, then read how it verifies and executes them.

**What Litex works with**

1. [Objects](https://litexlang.com/doc/Manual#objects): the mathematical terms and data-like structures Litex can talk about.
2. [Builtin Predicates](https://litexlang.com/doc/Manual#builtin-predicates): the common builtin predicates used to make atomic facts, such as `=`, `<`, `$in`, `$subset`, and `$is_set`.
3. [Factual Statements](https://litexlang.com/doc/Manual#factual-statements): how atomic facts combine into chains, conjunctions, disjunctions, `exist`, and `forall`.
4. [Statements](https://litexlang.com/doc/Manual#statements): the statement forms used to introduce definitions, context, and proof blocks.

**How Litex verifies facts**

1. [Builtin Verification Rules](https://litexlang.com/doc/Manual#builtin-verification-rules): the builtin steps that can close goals while checking a fact.
2. [Proof Process](https://litexlang.com/doc/Manual#proof-process): the end-to-end flow from writing statements to checked facts.

**How Litex executes code**

1. [Statements](https://litexlang.com/doc/Manual#statements): what each statement does when it is executed.
2. [Inference](https://litexlang.com/doc/Manual#inference): the extra execution step for accepted facts, adding consequences so later statements can use a richer context.

---

## Objects

_The whole is greater than the sum of its parts._

_— Aristotle_

### Objects as sets

Everything you write in a formula is built from a fixed menu of expression forms: numbers, identifiers, sets, functions, tuples, sums, and so on. We call these objects (they are not variables because in math anything is constant). And since Litex is set-based, all objects are sets.

The subsections below name each form in ordinary mathematical language and show typical Litex spelling.

Objects are the material that facts talk about. For the full path from objects to atomic facts, verification, storage, and inference, see [Proof Process](https://litexlang.com/doc/Manual#proof-process).

#### Names and parameters

Objects introduced by `forall`, `have`, `let`, and function parameters are atomic pieces of syntax—not built from smaller operators inside Litex.

```litex
forall x R:
    x = x
```

#### Function application

A function (given by `have fn` or by an anonymous head) applied to arguments denotes the value of the map at that point. Arguments may be grouped in several layers (curried style).

```litex
have fn f(x R) R = x + 1
f(2) = 3
```

#### Numeric literals

Decimal or integer numerals; they combine with `+`, `-`, `*`, `/`, `%`, `^`, etc.

```litex
1 + 2 = 3
```

#### Arithmetic and integer remainder

Binary operations on expressions; `%` is integer remainder when both sides are concrete integers; `^` is exponentiation.

```litex
2 * 3 = 6
5 % 2 = 1
2 ^ 3 = 8
```

#### `abs`, `log`, `max`, `min`

Absolute value, logarithm (base and argument follow Litex parsing rules), and binary maximum and minimum.

```litex
forall x R:
    0 <= x
    =>:
        abs(x) = x
```

#### Union, intersection, set difference

Set operations `A union B` and `A intersect B` (that is, union and intersection), and differences such as `set_minus` / `set_diff`. Keyword and infix forms are interchangeable.

```litex
2 $in union({1, 2}, {2, 3})
2 $in intersect({1, 2}, {2, 3})
have t set = set_minus({1, 2}, {1})
```

```litex
1 $in {1} `union {2}
```

#### Big union and big intersection (`cup`, `cap`)

Union and intersection over a **family** of sets (often written with an index); in Litex this is `cup(...)` and `cap(...)` on a suitable “set of sets.” Short illustrative proofs often need extra side conditions on the inner sets—see comments in `examples/litex_object_examples.lit`.

#### Power set

`power_set(X)` (often written as `P(X)`): all subsets of `X`, for the finite-style uses Litex supports here.

```litex
{1, 2} $in power_set({1, 2, 3})
```

#### Enumerated sets

Finite sets written as `{a, b, ...}`.

```litex
1 $in {1, 2, 3}
```

#### Set comprehension

Set-builder form: `{ z in T | condition on z }`.

```litex
have s set = { z N : z > 5 }
```

#### Function types and anonymous functions

A **function space** is written `fn(x S) T`; an anonymous function value can be written with a `'R(x){...}`-style head and applied directly.

```litex
have g set = fn(x R) R
```

```litex
'R(x){x + 1}(2) = 3
```

#### Cartesian product and dimension

`A cross B cross ...`; `cart_dim` gives the number of factors when the value is recognized as a product.

```litex
let d set:
    d = cart(R, Q)
$is_cart(d)
cart_dim(d) = 2
```

#### Projection from a product

Pick one factor of a Cartesian product.

```litex
proj(cart(R, Q), 1) = R
```

#### Tuples and length

Ordered tuples `(a1, ..., an)` and their length.

```litex
(1, 2) = (1, 2)
```

```litex
let e set:
    e = (2, 3)
$is_tuple(e)
tuple_dim(e) = 2
e[1] = 2
```

#### Counting members

Size of a finite enumerated set.

```litex
count({1, 2, 3}) = 3
```

#### Finite `sum` and `product`

Summation and products over a bounded integer index with one expression body (indexed by a name like `x`).

```litex
sum(1, 3, '(x Z) Z {x}) = sum(1, 2, '(x Z) Z {x}) + '(x Z) Z {x}(3)
```

#### Integer intervals as sets

Half-open `range(m, n)` and closed `closed_range(m, n)` as set-valued expressions (membership goals may need surrounding proofs).

```litex
have r set = range(0, 10)
have w set = closed_range(0, 1)
```

```litex
have q set = 0 `closed_range 1
```

#### Sequence- and matrix-style index sets

Some indexed objects use **sequence** types or matrix index domains (repeated indices, `closed_range` on each axis) instead of a single `sum` index. Typical patterns appear with `family … fn(i …, j …) …` and `have fn M(i …, j …) …` (see below).

#### Choice (`choose`)

From a family of nonempty sets, pick an element from each member once typing guarantees nonemptiness.

```litex
let s nonempty_set:
    forall x s:
        $is_nonempty_set(x)
choose(s) $in s
```

#### Standard number sets

Names such as `R`, `Q`, `Z`, `N`, `N_pos`, and related signed or punctured variants.

```litex
0 $in Z
```

#### Parametric `family`

A definition `family name(…) = …` is instantiated by `\name(args)` to get a concrete set or function space.

```litex
family fam(s set) = fn(x N_pos) s
forall a \fam(R):
    a $in fn(y N_pos) R
```

#### Matrices

Litex supports matrices in three related ways: a constructor **type** `matrix(S, row_count, col_count)`, **literal** rectangular arrays `[[row1], [row2], …]`, and the same **indexed function space** pattern used for “matrices as maps” from a row–column index set into `S`.

**Type and literal.** You can bind a matrix object to a literal and read entries with two indices (like applying a function of two arguments):

```litex
prove:
    matrix(R, 2, 2) = matrix(R, 2, 2)

    have a matrix(R, 2, 2) = [[1, 2], [3, 4]]

    a $in fn (x1 N_pos, x2 N_pos: x1 <= 2, x2 <= 2) R

    a(1, 1) = 1
    a(1, 2) = 2
    a(2, 1) = 3
    a(2, 2) = 4
```

**Matrix algebra (surface operators).** These are **not** the scalar operators `+`, `-`, `*`, `^`. For two matrices of matching shape, `++` is cell-wise sum and `--` cell-wise difference. For compatible sizes, `**` is matrix product (columns of the left match rows of the right). For scalar `c` and matrix `A`, `c *. A` is scalar multiplication. For a square matrix and exponent `n` in `N_pos`, `A ^^ n` is matrix power.

```litex
eval [[1, 0], [0, 1]] ++ [[1, 0], [0, 1]]
```

```litex
eval [[2, 0], [0, 2]] -- [[1, 0], [0, 1]]
```

```litex
eval [[1, 2], [0, 1]] ** [[1, 0], [1, 1]]
```

```litex
eval 3 *. [[1, 2], [4, 5]]
```

```litex
eval [[2, 0], [0, 2]] ^^ 2
```

**Named matrices.** The same operators work on matrix objects (e.g. after `have m matrix(R, 2, 2) = …`).

```litex
have m matrix(R, 2, 2) = [[1, 0], [0, 1]]

eval m ++ m

eval m ** m

eval 2 *. m
```

**Indexed definition (`family` + `have fn`).** You can define the space of all `m x n` matrices over `S` as a binary-indexed function set, then give one `case` per index pair, useful for proofs that branch on `(i, j)`:

```litex
family self_matrix(s set, m, n N_pos) = fn(i closed_range(1, m), j closed_range(1, n)) s
```

Full worked proofs (for example a diagonal matrix claim and `$is_diagonal_matrix`) use the same `family` / `prop` / `claim` layout as in longer packaged examples. A compact illustration (not run as an isolated doc test):

<!-- litex:skip-test -->

```litex
family self_matrix(s set, m, n N_pos) = fn(i closed_range(1, m), j closed_range(1, n)) s

prop is_diagonal_matrix(n N_pos,m \self_matrix(R, n, n)):
    forall i closed_range(1, n), j closed_range(1, n):
        i != j
        =>:
            m(i, j) = 0

claim:
    prove:
        forall M \self_matrix(R, 3, 3):
            M(1, 1) = 1
            M(1, 2) = 0
            M(1, 3) = 0
            M(2, 1) = 0
            M(2, 2) = 1
            M(2, 3) = 0
            M(3, 1) = 0
            M(3, 2) = 0
            M(3, 3) = 1
            =>:
                $is_diagonal_matrix(3, M)

    by for:
        prove:
            forall i closed_range(1, 3), j closed_range(1, 3):
                i != j
                =>:
                    M(i, j) = 0
```

---

## Factual Statements

_I think, therefore I am._

_— René Descartes_

A **factual statement** is a Litex statement that claims a mathematical fact. It may be as small as `1 = 1`, or as structured as a `forall`, `exist`, `or`, or chain of inequalities.

The result of checking a factual statement is either **true** or **unknown**.

- **true** means Litex has verified the fact from the current context, definitions, and builtin rules.
- **unknown** means Litex does not have enough verified information to close the goal. The fact may be false, or it may simply need more intermediate facts.

Once a factual statement is verified, it becomes a **known fact** in the current context and can be reused by later statements.

> Hint: `unknown` is usually a request for a smaller step. Try stating the missing equality, membership, domain condition, or previous lemma explicitly.

This page is about **facts themselves**. For the larger list of Litex statement forms such as `prop`, `have`, `claim`, `prove`, `know`, and `witness`, see [Builtin statements](https://litexlang.com/doc/Manual#statements).

This page mainly lists the **types of facts** Litex can read and how they are shaped. For how those facts are actually proved by the checker, read [Proof Process](https://litexlang.com/doc/Manual#proof-process) and [Builtin Verification Rules](https://litexlang.com/doc/Manual#builtin-verification-rules).

---

### Quick mental model

Think of Litex as checking one sentence at a time:

```litex
1 + 1 = 2
```

Litex asks:

1. Are the terms well-defined?
2. What shape is this fact?
3. Can the fact be proved from what is already known?
4. If the fact is compound, can its smaller parts be checked?

For example:

```litex
have x R = 2
x + 1 = 3
```

The second line works because `x` is already known to be `2`, so the equality can be reduced to a numeric equality.

---

### Shapes of facts

Different fact shapes are verified in different ways, but they all reduce to the same idea: Litex must justify the claim from the current context.

| Shape | Meaning | Example |
|-------|---------|---------|
| **Atomic fact** | One basic claim: equality, order, membership, or one predicate call. | `1 = 1`, `2 < 3`, `1 $in {1, 2}`, `$is_set(R)` |
| **Atomic negation** | Negation of one atomic claim. | `2 != 3`, `not 1 < 0` |
| **Conjunction** | Several atomic facts all hold. | `1 = 1 and 2 < 3` |
| **Chain** | Shorthand for adjacent comparisons. | `0 < 1 < 2` |
| **Disjunction** | At least one branch holds. | `1 = 2 or 1 = 1` |
| **Existential fact** | **Inline witness form**: `exist`, `exist!`, or `not exist`, followed by `st { ... }`. | `exist x R st { x = 1 }` |
| **Universal fact** | For all typed variables, conclusions hold. | `forall! x R: x = x`, or block `forall x R:` |
| **Universal with equivalence** | A universal fact with an equivalent reformulation. | block `forall ...` with `<=>:` |
| **Negated universal** | A universal claim is false. | `not forall x R: x > 0` |

---

### Atomic facts

An **atomic fact** is one indivisible mathematical claim. It is made from a **predicate** and its **arguments**. The predicate is the judgment being made; the arguments are the objects being judged. Some predicates are built into Litex because they correspond to basic mathematical ideas, such as equality `=`, order `>`, membership `$in`, subset `$subset`, and set predicates like `$is_set`.

If [Objects](https://litexlang.com/doc/Manual#objects) are the mathematical things you talk about, predicates are the basic ways to make judgments about them. In ordinary mathematical language, they are the verbs of small facts:

```text
1 + 1       // an object
1 + 1 = 2   // a fact
2           // an object
2 $in N     // a fact
```

Common atomic facts:

```litex
1 + 1 = 2
```

Here `=` is the main relation(predicate), and `1 + 1` and `2` are the arguments. This factual statement is true by calculation.

> Note: In Litex, expressions such as `1 + 1`, `x - y`, or `f(x)` are usually treated as **objects** or **terms**. They name values. They are not facts by themselves, so they are not true or false.

> Note: The **verb** of a factual statement is the part that makes a judgment: `=`, `!=`, `<`, `$in`, `$is_set(...)`, or a custom predicate such as `$is_one(...)`. For example, `1 + 1` has no truth value, but `1 + 1 = 2` does.

> Hint: When reading an atomic fact, first find the verb that is being checked. The remaining pieces are the objects the verb talks about.

More examples with builtin predicates:

```litex
2 != 3
0 < 1
not 1 < 0
1 $in {1, 2}
$is_set({1, 2})
```

> Note: Builtin predicates and builtin objects are connected by many builtin verification rules. These predicates and rules are the common concepts and rules from basic mathematics, not advanced hidden machinery. Each single rule is usually intuitive: for example, `1 $in {1, 2}`, `2 < 3`, `2 != 3`, or `$is_set({1, 2})`. The surprising part is the total size of the background knowledge. Basic mathematics has many small relationships, and Litex has hundreds of them built in for standard numbers, sets, functions, tuples, comparisons, equality, and membership.

> Note: Because of this, using builtin predicates and builtin objects is often much more convenient than rebuilding the same ideas with custom predicates. When you write facts with standard forms such as `$in`, `$is_set`, `=`, `<`, `R`, `Z`, or `{1, 2}`, Litex can often use hundreds of built-in relationships behind the scenes.

> Hint: Prefer builtin predicates and builtin objects when they express what you mean. Use custom `prop` definitions when you need a new mathematical idea that is not already covered by the builtin vocabulary.

Custom predicates defined by `prop` are also atomic when you call them:

```litex
prop is_one(x R):
    x = 1

$is_one(1)
```

The call `$is_one(1)` is atomic. Litex can unfold the `prop` definition and check that `1 = 1`.

> Hint: A predicate definition is written with `prop is_one(...)`, but a predicate fact is called with `$is_one(...)`.

Atomic facts are usually checked by:

- direct computation, such as `2 + 3 = 5`;
- known definitions, such as a `prop` body or a `have fn` equation;
- already known facts in the current context;
- builtin verification rules for equality, order, membership, sets, tuples, numbers, and similar standard objects.

> Hint: Before Litex proves an atomic fact, it must also know that the expressions make sense. For example, using a variable usually requires that the variable has already been introduced with a type such as `have x R`.

---

### Conjunctions

A **conjunction** says that several atomic facts all hold.

```litex
1 = 1 and 2 < 3
```

This means the same thing as writing the two facts separately:

```litex
1 = 1
2 < 3
```

Litex style usually prefers the second form. It is easier to read, and when something becomes `unknown`, the failing line is clearer.

> Hint: Use `and` inside compact bodies such as `exist x R st { ... }` only when it improves readability. In ordinary proof blocks, one fact per line is usually better.

---

### Chains

A **chain** is a compact way to write adjacent binary relations.

```litex
0 < 1 < 2
```

Logically, this means:

```litex
0 < 1 and 1 < 2
```

Chains are not a new kind of mathematical logic. They are shorthand for smaller atomic comparisons, and Litex may also use order facts to derive convenient consequences.

```litex
0 < 1 < 2
0 < 2
```

When several comparisons belong to the same ordered path, prefer a chain such as `a < b < c` instead of writing separate facts such as `a < b` and `b < c`. The chain is shorter, shows the structure more clearly, and gives Litex a direct shape for applying builtin order support.

> Hint: If a chain is hard to debug, split it into its adjacent pieces first.

> Hint: Try to use `<` consistently instead of switching back and forth between `<` and `>`. For example, prefer `a < b < c` over `c > b > a` when either form would say the same thing. A consistent direction makes proof steps easier to read and easier for builtin order rules to match.

---

### Disjunctions

A **disjunction** says that at least one branch holds.

```litex
1 = 2 or 1 = 1
```

Litex can verify this because the second branch is true.

A branch is usually an atomic fact, a conjunction of atomic facts, or a chain.

> Hint: To prove `A or B`, it is enough for Litex to prove one side.

Disjunctions also work together with the `by cases` statement. After Litex knows `A or B`, `by cases` can split the proof into one branch where `A` is assumed and another branch where `B` is assumed.

```litex
have x R

by cases:
    prove:
        x = 0 or x != 0
    case x = 0:
        ...
    case x != 0:
        ...
```

> Hint: Think of `or` as the factual statement shape, and `by cases` as the proof statement that uses that shape.

---

### Existential facts

An **existential fact** says that there is a witness satisfying some conditions.

```text
exist x R st { x = 1 }
```

Read this as: there exists an `x` in `R` such that `x = 1`.

You can also state uniqueness:

```text
exist! x R st { x = 0 }
```

And non-existence:

```text
not exist x R st { x != x }
```

The body after `st` is the list of facts the witness must satisfy.

> Hint: To prove an `exist` goal, Litex usually needs a concrete witness. In proof code, use `witness` when you want to tell Litex which object should be used as the witness.

> Hint: To use an already known `exist` fact, use `have by exist` to give names to the witnesses and bring their body facts into the current context.

Example:

```litex
know exist u R st { u = 1 }

have by exist v R st { v = 1 }: h
h = 1
```

---

### Universal facts

A **universal fact** says that something holds for every object of a given type.

```litex
forall x R:
    x = x
```

Read this as: for every `x` in `R`, `x = x`.

A universal fact can also have assumptions before `=>:`:

```litex
forall x R:
    0 < x
    =>:
        x != 0
```

Read this as: for every `x` in `R`, if `0 < x`, then `x != 0`.

The lines before `=>:` are the **domain assumptions** or **hypotheses**. The lines under `=>:` are the **conclusions**.

> Hint: Without assumptions, put conclusions directly under `forall`. With assumptions, put the assumptions first, then `=>:`, then indent the conclusions one more level.

Compact `forall!` syntax is also available for short facts:

```litex
forall! x R => {x = x}
forall! x R: x > 0 => {x != 0}
```

For beginners, block form is often clearer.

---

### Universal facts with equivalence

Sometimes a universal statement says that two descriptions are equivalent. Litex writes this with `<=>:`.

```litex
forall x, y R:
    =>:
        x > y
    <=>:
        y < x
```

Read this as: under the same variables and assumptions, `x > y` is equivalent to `y < x`.

> Hint: Use `<=>:` when both directions are intended. If you only need one direction, use an ordinary `forall` with `=>:`.

---

### Negated universal facts

A **negated universal** says that a universal claim is not true.

```text
not forall x R:
    x > 0
```

Read this as: it is not true that every real number is greater than `0`.

> Hint: `not forall` is different from putting `not` inside the conclusion. If you want to say there is a counterexample to a universal claim, use `not forall`.

---

## Builtin Predicates

_Geometry, like arithmetic, requires for its logical development only a small number of simple, fundamental principles._

_- David Hilbert_

This page lists the **builtin predicates** that Litex recognizes as atomic facts. It follows the atomic fact forms handled by the kernel.

For the general idea of atomic facts, including the idea that a fact is made from a predicate and its arguments, read [Factual Statements](https://litexlang.com/doc/Manual#factual-statements). For how these predicates are proved automatically, read [Builtin Verification Rules](https://litexlang.com/doc/Manual#builtin-verification-rules).

---

### Equality and Order

These predicates compare two objects, usually numeric expressions.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `a = b` | `a != b` | `a` and `b` denote the same value. |
| `a < b` | `not a < b` | `a` is strictly less than `b`. |
| `a > b` | `not a > b` | `a` is strictly greater than `b`. |
| `a <= b` | `not a <= b` | `a` is less than or equal to `b`. |
| `a >= b` | `not a >= b` | `a` is greater than or equal to `b`. |

---

### Set Predicates

These predicates say what kind of set-like object Litex is seeing.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `$is_set(A)` | `not $is_set(A)` | `A` is treated as a set object. |
| `$is_nonempty_set(A)` | `not $is_nonempty_set(A)` | `A` has at least one element. |
| `$is_finite_set(A)` | `not $is_finite_set(A)` | `A` is finite in the sense Litex uses for standard finite objects. |

---

### Membership

Membership is the set-theoretic version of a type assertion.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `x $in A` | `not x $in A` | `x` is an element of `A`. |

---

### Shape Predicates

These predicates recognize common data shapes.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `$is_cart(C)` | `not $is_cart(C)` | `C` is a Cartesian product. |
| `$is_tuple(t)` | `not $is_tuple(t)` | `t` is a tuple value. |

---

### Set Inclusion

These predicates express inclusion between sets.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `A $subset B` | `not A $subset B` | Every element of `A` belongs to `B`. |
| `A $superset B` | `not A $superset B` | Every element of `B` belongs to `A`. |

---

### Function Restriction

This predicate says whether a function can be viewed as having a smaller or more constrained function type.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `f $restrict_fn_in T` | `not f $restrict_fn_in T` | `f` can be restricted to the function space `T`. |

---

### Function Equality

These predicates express equality of functions.

| Predicate | Meaning |
|-----------|---------|
| `$fn_eq_in(f, g, S)` | `f` and `g` agree at every argument in `S`. |
| `$fn_eq(f, g)` | `f` and `g` are globally equal as function values. |

---

### Not Builtin: User Predicates

Calls such as `$p(x)` are also atomic facts, but they are not builtin predicates. They come from user declarations such as `prop p(...)` or `abstract_prop p(...)`, and Litex verifies them from the user's definition or known facts.

---

## Statements

_If you can't explain it to a six year old, you don't understand it yourself._

_- Albert Einstein_

A **statement** is a basic line or block of Litex code. You use statements to do mathematical reasoning, make definitions such as `prop`, functions, and sets, and prove facts from known facts or axioms.

This page is a practical reference. Read each section as: **what the statement means**, **when to use it**, and **what shape the code usually has**.

Statements are the outer actions in a Litex file. Some statements contain [Factual Statements](https://litexlang.com/doc/Manual#factual-statements), which are checked through the flow described in [Proof Process](https://litexlang.com/doc/Manual#proof-process).

---

### Assert a fact

Write a fact directly when you want Litex to verify it from what is already known. Facts include equality, order, membership, `forall`, `exist`, and compound facts with `and` / `or`.

```litex
1 + 1 = 2
```

> Hint: A bare fact should already follow from the current context. If you want to prove a fact in a sub-proof and add only the final fact back to the current context, use `claim:`.

Common fact types:

| Kind | Fact type | Example |
|------|-----------|---------|
| Atomic fact | Equality | `1 + 1 = 2` |
| Atomic fact | Inequality / order | `2 < 3`, `3 <= 3` |
| Atomic fact | Membership | `2 $in R` |
| Atomic fact | Predicate fact | `$prime(17)` |
| Atomic fact | Atomic negation | `2 != 3`, `not 1.1 $in Z` |
| Compound fact | Conjunction | `1 < 2 and 2 < 3` |
| Compound fact | Disjunction | `1 < 2 or 1 >= 2` |
| Compound fact | Chain | `1 <= 2 = 2 < 3` |
| Quantified fact | Existence | `exist x R st {x > 0}` |
| Quantified fact | Unique existence | `exist! x R st {x = 0}` |
| Quantified fact | Universal fact | `forall! x R: x = x` |

For a fuller explanation, see [Factual Statements](https://litexlang.com/doc/Manual#factual-statements).

---

### Named predicate (`prop`)

Use **`prop`** to name a mathematical property. The body says what the property means.

After a `prop` is defined, Litex can verify later predicate facts by using that definition. In the example below, `$p(1)` holds because `1 $in R` and `1 = 1`.

```litex
prop p(x R):
    x = x

$p(1)
```

> Example: after defining `prop p(x R): ...`, you can write `$p(1)` instead of repeating the definition each time.

---

### Abstract predicate symbol (`abstract_prop`)

Use **`abstract_prop`** when you want a predicate symbol but do not want to define it yet. It only declares the name; it does not give the predicate any mathematical property by itself.

If you want an abstract predicate to have a property, introduce that property with `know`.

```litex
abstract_prop p(x)

know forall x R:
    $p(x)

$p(1)
```

> Hint: `abstract_prop` is useful for examples, axiomatized theories, and temporary placeholders while developing a proof.

---

### Typed parameters (`have`)

Use **`have x S`** to introduce a new object `x` of `set` or `nonempty_set` or `finite_set` or set like `R`(real numbers), `Z`(integers), `{1, 2, 3}`(enumerated set), `cart(R, Z)`(Cartesian product), etc. We say `x` has *type* `S`.

```litex
have x R, y Z
```

This records that `x` belongs to `R` and `y` belongs to `Z`, so later facts can use them.

> Hint: `have x S` is not a free way to create an element of any set. Litex must be able to verify that `S` is nonempty, for example by knowing `$is_nonempty_set(S)`, before it can introduce a new object `x` with `x $in S`.

### What "type" means in Litex?

The word **type** in Litex does not mean a type in type theory. Litex is based on set theory. A parameter type is one of a few surface forms:

```litex
have x R
have A set
have B nonempty_set
have C finite_set
```

`have x R` means `x $in R`: the "type" `R` is a set that contains `x`.

`set`, `nonempty_set`, and `finite_set` are closer to actions than ordinary object types. They introduce a new name and record facts about it:

```litex
have A set
have B nonempty_set
have C finite_set

$is_set(A)
$is_nonempty_set(B)
$is_finite_set(C)
```

Since Litex follows the set-theoretic view, every object you introduce is an object in the set-theoretic universe. In this sense, `$is_set(x)` holds for any introduced object `x`.

The same parameter-type idea also appears in `forall`, `exist`, `prop`: you can write parameters such as `forall x R, y set:` or `exist A set st { ... }`. Function signatures are more restrictive. When defining a function, each input position must use an object as its domain, such as `fn(x R) Z`; you cannot use action-like forms such as `set`, `nonempty_set`, or `finite_set` as a function input requirement.

---

### Defined constant (`have … = …`)

Use **`have a S = expr`** to introduce a name and fix its value. For example, `have a R = 1` introduces a constant `a` with value `1` and in set `R`.

```litex
have a R = 1
a = 1
```

> Hint: use this for constants. A function should normally be introduced with `have fn`.

---

### Naming witnesses (`have by exist`)

When an existential fact is already known, **`have by exist`** gives names to its witnesses. After that, you can use the witness properties directly.

```litex
know exist u R st {u > 0, u < 1}
have by exist v R st {v > 0, v < 1}: w
w > 0
```

---

### Function from one defining equation (`have fn … = …`)

Use **`have fn f(x S) T = body`** when the value of the function is given by one expression.

```litex
have fn f(x R) R = x + 1

forall x R:
    f(x) $in R
    f(x) = x + 1
```

> Example: this says that for each `x R`, the value `f(x)` satisfies `f(x) $in R` and `f(x) = x + 1`.

---

### Piecewise function (`have fn` with `case`)

Use **`case`** branches when the formula for a function depends on conditions.

```litex
have fn g(z R) R :
    case z = 2: 3
    case z != 2: 4

forall z R:
    g(z) $in R

forall z R:
    z = 2
    =>:
        g(z) = 3

forall z R:
    z != 2
    =>:
        g(z) = 4
```

> Hint: the cases should cover the domain you intend to use.

---

### Function from unique existence (`have fn … by forall … exist!`)

Use this when mathematics tells you that for every input there exists a **unique** output. Litex then introduces the corresponding function.

```litex
abstract_prop p(x)
abstract_prop F(x, y)
have A set
have B set

know forall x A:
    $p(x)
    =>:
        exist! y B st {$F(x, y)}

have fn f by forall x A:
    $p(x)
    =>:
        exist! y B st {$F(x, y)}

forall x A:
    $p(x)
    =>:
        $F(x, f(x))
```

> Meaning: the unique witness `y` is now named by the function value `f(x)`.

> Hint: the `forall` after `by` must already be known. Its conclusion must be exactly one `exist!` fact with one output parameter.

---

### Function by induction on a parameter (`have fn by induc`)

Use **`have fn by induc`** to define a function on an inductive domain, such as nonnegative integers. Base cases and the recursive step are written as `case` branches.

The intended meaning is close to strong induction for defining a function. The first `case` lines give the starting values. The final `case x >= ...:` is the recursive step: when defining `h(x)`, the right-hand side may use values of the same function that are already defined, from the starting value up to `x - 1`. It may not use `h(x)` itself or any later value such as `h(x + 1)`.

If the final recursive step has nested `case` branches, those branches should cover all possible situations for the current `x`. They should also behave like a real case split: overlapping branches must not give conflicting values. If two branches can both apply, their right-hand sides should be provably equal under the overlap.

```litex
know forall x Z:
    x % 2 = 0 or x % 2 = 1

have fn by induc from 0: h(x Z: x >= 0) R:
    case x = 0: 1
    case x = 1: 1
    case x >= 2:
        case x % 2 = 0: h(0) + h(x - 1)
        case x % 2 = 1: h(x - 2) + h(x - 1)
```


---

### Object definition without  (`let`)

Use **`let`** to introduce names together with assumptions or definitions about them. The names are local to the surrounding proof or block.

```litex
let a R:
    a = 1
a = 1

let b, c R: b < c

b < c
```

> Hint: `let` and `know` both introduce new facts without verification. Litex allows this and warns you because these statements are useful when you intentionally add axioms or temporary assumptions, but abusing them can make the system unsound. In most cases, do not use them; use `have`, a bare fact, or `claim` when you want Litex to verify the reasoning.

---

### Parametric family (`family`)

**`family name(params) = …`** defines a parameterized set or function space; instantiate it with **`\pf(R)`**-style syntax (backslash then the family name and arguments).

A `family` is different from a function introduced by `have fn`. A function is an object that takes input values. A `family` is a template for building an object, usually a set or a function space. Because it is only a template, its parameters can use forms such as `s set`. Each time you write `\self_seq(R)`, Litex substitutes `R` for `s` in the right-hand side of the family definition and uses the resulting object.

```litex
family self_seq(s set) = fn(x N_pos) s

forall a \self_seq(R):
    a $in fn(y N_pos) R
    a(1) = a(1)
```

---

### Algorithm and evaluation (`algo` / `eval`)

**`algo m(x):`** gives an executable presentation of a function (often parallel to **`have fn`**). **`eval m(…)`** runs that algorithm on concrete inputs to simplify results.

An `algo` is not the same as a function in a programming language such as Python. When you define an `algo`, Litex checks that the case flow really matches the function facts you have given. In the example below, the two cases must agree with the definition of `m`.

`algo` also does not compute by floating-point approximation. It works with exact symbolic arithmetic, so the current evaluator only supports operations such as `+`, `-`, `*`, and integer powers.

```litex
have fn m(x N_pos) R:
    case x = 1: 1
    case x != 1: 0

algo m(x):
    case x = 1: 1
    case x != 1: 0

eval m(1)
m(1) = 1
```

```litex
have g fn(x Z) Z

know:
    forall x Z:
        x > 0
        =>:
            g(x) = g(x-1) + 1
    g(0) = 0
    forall x Z:
        x < 0
        =>:
            g(x) = g(x+1) - 1

algo g(x):
    case x > 0: g(x-1) + 1
    case x = 0: 0
    case x < 0: g(x+1) - 1

eval g(3)
g(3) = 3
```

> Hint: Like algorithms in ordinary programming languages, an `algo` can still run forever during evaluation if its recursive calls do not terminate.

---

### Claim (`claim`)

**`claim:`** states a goal and bundles a sub-proof (and optional lemmas) that establishes it.

The point of `claim` is that the proof process does not enter the main environment. The temporary facts used inside the proof stay inside the claim; only the final fact you wanted to prove is added to the surrounding context.

```litex
claim:
    prove:
        1 + 1 = 2
    1 + 1 = 2

claim:
    prove:
        2 = 2
    2 = 2

# inline claim: put the goal on the header line
claim 3 = 3:
    3 = 3

claim forall! x R => {x = x}:
    x = x
```

---

### Assume known facts (`know`)

**`know:`** (or **`know`** with a block) adds lemmas or axioms to the current environment without proving them in this snippet.

> Hint: `know` is an axiom-like statement. Litex allows it and warns you, but in most ordinary proofs you should prefer facts that Litex verifies directly, or use `claim` to prove a fact in a sub-proof before adding it to the context.

```litex
# three primitive terms:
have point nonempty_set
have line nonempty_set
have plane nonempty_set

# All elements on a line or a plane are points (power_set: the set of all subsets of a set)
know:
    forall l line:
        l $in power_set(point)
    forall pl plane:
        pl $in power_set(point)
```

---

### Nested proof (`prove`)

**`prove:`** opens a lemma or sub-proof: a nested list of statements closed before the parent continues.

It does not affect the outside environment at all. You can think of it as a scratch space for checking a piece of reasoning: facts introduced or proved inside the `prove` block disappear when the block ends.

```litex
prove:
    2 = 2
```

---

### run file

**`run_file "path.lit"`** runs a file as a separate episode. Paths and project layout decide what works in your setup; use the same quoting style your toolchain expects.

```text
run_file "local_path_to_file.lit"
```

---

### No-op (`do_nothing`)

A trivial proof step (placeholder or explicit skip). Write `do_nothing` or `...` to skip a proof step.

```litex
do_nothing
...
```

---

### Clear environment (`clear`)

**`clear`** drops the current top environment and parse-time name map so later lines start fresh (often used so a second `let` with the same name is allowed in a new block).

```litex
let a R:
    a = 1
a = 1

clear

let a R:
    a = 2
a = 2
```

---

### Evaluate an expression (`eval`)

Besides algorithms, **`eval expr`** can reduce closed expressions according to evaluation rules.

```litex
eval [[1, 0], [0, 1]] ++ [[1, 0], [0, 1]] # matrix addition

eval sum(1, 2, '(x Z) Z {sum(2, 3, '(y Z) Z {x + y})}) # sum of a sum
```

---

### Witness for `exist` (`witness exist`)

**`witness exist … from …:`** supplies explicit values and a sub-proof that they satisfy the existential body, concluding **`exist …`**.

Existence proofs are often used together with `have by exist`: first prove that some object exists, then name the witness so later lines can use an object with the stated properties.

```litex
witness exist x, y R st {x > y} from 1, 0:
    1 > 0

exist a, b R st {a > b}

have by exist x, y R st {x > y}: w, z
w > z
```

---

### Witness non-emptiness (`witness $is_nonempty_set`)

Shows a set is nonempty by naming a member and proving membership.

```litex
witness $is_nonempty_set({1, 2, 3}) from 1:
    1 $in {1, 2, 3}

$is_nonempty_set({1, 2, 3})
```

---

### Proof by cases (`by cases`)

Splits a goal along a finite disjunction; each **`case`** branch finishes the goal under that assumption.

```litex
have fn k(z R) R :
    case z = 2: 3
    case z != 2: 4

have x R

x = 2 or x != 2

by cases:
    prove:
        k(x) > 2
    case x = 2:
        k(x) = 3
        k(x) > 2
    case x != 2:
        k(x) = 4
        k(x) > 2

# inline by cases: put the goal on the header line
by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1
```

---

### Proof by contradiction (`by contra`)

Assumes the positive form of a statement, derives a contradiction (`impossible`), and concludes the negation.

```litex
abstract_prop p0(x, y)
abstract_prop q0(x, y)

know forall a, b R:
    $p0(a, b)
    =>:
        $q0(a, b)

know not $q0(1, 2)

by contra:
    prove:
        not $p0(1, 2)
    $p0(1, 2)
    impossible $q0(1, 2)

# inline example
by contra not $p0(1, 2):
    $p0(1, 2)
    impossible $q0(1, 2)
```

---

### Enumerate a finite set (`by enumerate finite_set`)

Finite “for all members of this enumerated set” reasoning—useful for small domains and Cartesian products of finite sets.

```litex
let a R:
    a $in {1, 2}

a = 1 or a = 2

by enumerate finite_set:
    prove:
        forall a2 {1, 2, 3}:
            a2 < 4

# inline by enumerate finite_set: put the forall goal on the header line
by enumerate finite_set forall! a2 {1, 2, 3} => {a2 < 4}:
    ...
```

---

### Induction (`by induc`)

**`by induc n from base:`** proves **`P(n)`** for a discrete parameter from a base and step known (or proved) in the environment.

```litex
abstract_prop r0(a)

know:
    $r0(0)
    forall n Z:
        n >= 0
        $r0(n)
        =>:
            $r0(n + 1)

by induc n from 0:
    prove:
        $r0(n)

forall m Z:
    m >= 0
    =>:
        $r0(m)
```

> Hint: Many `by ...` statements are not random proof commands. They match the logical shape of the factual statement you are trying to prove or use. For example, `by cases` matches an `or` fact, `by contra` matches negation, and `by induc` matches an inductive or universal pattern over a discrete domain. Other `by ...` statements are tied to specific object structures: `by for` works with bounded ranges, `by enumerate` works with finite objects, and `by extension` works with set equality.



---

### Bounded iteration shell (`by for`)

**`by for:`** packages a proof skeleton that iterates over a bounded index set (e.g. a **`range`**).

```litex
by for:
    prove:
        forall i range(0, 10):
            i < 10
    do_nothing

# inline by for: put the forall goal on the header line
by for forall! i range(0, 10) => {i < 10}:
    do_nothing
```

---

### Set equality by extensionality (`by extension`)

Proves **`A = B`** by mutual inclusion, often with **`by enumerate finite_set`** on each side.

```litex
by extension:
    prove:
        {1, 2} = {2, 1}
    by enumerate finite_set:
        prove:
            forall x {1, 2}:
                x $in {2, 1}
    by enumerate finite_set:
        prove:
            forall y {2, 1}:
                y $in {1, 2}

{1, 2} = {2, 1}
```


---

### Enumerate a closed integer interval (`by enumerate ……`)

For **`x`** known to lie in **`closed_range(lo, hi)`**, **`by enumerate lo...hi: x`** runs the finite enumeration tactic on that interval.

```litex
have x closed_range(0, 10)

by enumerate 0...10: x
```

```litex
have a Z
have x closed_range(a, a + 10)

by enumerate a...a + 10: x
```

---

### Set-theoretic bridge tactics (`by fn`, `by family`, `by tuple`, `by fn set`)

These statements are usually not the most useful things to write in ordinary proofs. They exist mainly so every object that appears in Litex has a definite set-theoretic meaning. For example, a function is represented by graph-style facts, a tuple by its components and product typing, and a `family` instance by substituting arguments into its template.

| Statement | What it connects to |
|-----------|---------------------|
| `by fn: f` | The graph-style facts behind a known function `f` |
| `by family: \pf(R)` | The object obtained by substituting `R` into a `family` template |
| `by tuple: u` | The set-theoretic structure of a tuple object |
| `by fn set: s $in fn(...) ...` | The graph-style conditions that make a set behave as a function |

> Hint: Most users do not need these statements at first. They are mainly semantic bridge tools: useful when you need to expose the set-theoretic object behind a Litex surface form.

---

### Statement summary

The sections above explain the common use cases. This table is a quick map of the statement families.

| Statement | Main use |
|-----------|----------|
| fact line | Verify a mathematical fact from the current context |
| `prop` | Define a named mathematical property |
| `abstract_prop` | Declare a predicate symbol without defining it |
| `have x S` | Introduce an object with a type or set |
| `have x S = expr` | Introduce a named value |
| `have by exist` | Name witnesses from a known existential fact |
| `have fn ... = ...` | Define a function by one formula |
| `have fn ... : case ...` | Define a function by cases |
| `have fn ... by forall ... exist!` | Define a function from unique existence |
| `have fn by induc` | Define a recursive function by induction |
| `let` | Introduce local names and local assumptions |
| `family` | Define a parameterized set or function space |
| `algo` / `eval` | Define and run executable mathematical algorithms |
| `claim` | State a goal and prove it in a sub-block |
| `know` | Add facts or axioms to the current context |
| `prove` | Open a nested proof block |
| `import` / `run_file` | Use code from another file |
| `do_nothing` | Explicit no-op proof step |
| `clear` | Reset the current working context |
| `witness exist` | Prove an existential by giving witnesses |
| `witness $is_nonempty_set` | Prove a set is nonempty by giving an element |
| `by cases` | Prove a goal by splitting into cases |
| `by contra` | Prove by contradiction |
| `by enumerate finite_set` | Check a finite list of cases |
| `by enumerate n...m` | Check a finite integer interval `n <= x <= m` |
| `by induc` | Prove a statement by induction |
| `by for` | Run a bounded proof skeleton |
| `by extension` | Prove set equality by mutual membership |
| `by fn` / `by fn set` / `by family` / `by tuple` | Expose the set-theoretic meaning behind function, family, and tuple objects |

> Hint: when learning Litex, start with `have`, `know`, bare facts, `claim`, and `by cases`. The other statements become useful when your proofs need definitions, functions, induction, or finite enumeration.

---

## Proof Process

_Beware of bugs in the above code; I have only proved it correct, not tried it._

_- Donald Knuth_

A Litex proof is built from facts you claim one after another. After a fact is proved, it becomes known information for proving the next facts.

This page explains how one fact gets proved. The process is designed to stay close to ordinary mathematical thinking: first check that expressions make sense, then try direct mathematical rules, reuse known facts, and instantiate known universal facts when their shape matches the goal.

---

### The Core Loop

Most verification in Litex follows the same loop:

1. Check that the fact is well-defined.
2. Try builtin mathematical rules.
3. Try matching known facts.
4. Try matching known `forall` facts.

The exact details depend on the shape of the fact, but this loop is the main mental model.

#### A builtin rule proves it

Some facts are closed directly by builtin mathematical rules.

```litex
2 + 3 = 5
```

Here Litex does not need a previous lemma. It evaluates the arithmetic expression and closes the equality by calculation. Other builtin rules handle ordinary mathematical background such as order, membership, set predicates, tuples, functions, and standard equality patterns. See [Builtin Verification Rules](https://litexlang.com/doc/Manual#builtin-verification-rules) for the detailed list.

#### The same fact is already known

Some facts are true because the current context already contains the same fact.

```litex
abstract_prop ok(x)
know $ok(0)
$ok(0)
```

The last line is accepted because `$ok(0)` is already known in the proof context. This is the simplest form of reuse: a fact proved or introduced earlier can be used later.

#### A known `forall` proves it

Known universal facts are also reusable. Litex can match the current goal against a known `forall` statement and substitute the right argument.

```litex
abstract_prop p(x)
know forall x R:
    $p(x)
$p(2)
```

The known fact says that every real number satisfies `$p`. When the goal is `$p(2)`, Litex matches `x` with `2` and checks the instantiated conclusion.

This match-and-substitution behavior is one of the main reasons Litex proofs can be written without manually naming every small intermediate fact.

---

### Atomic Fact Verification

An **atomic fact** is one indivisible mathematical claim, such as:

```text
2 + 3 = 5
2 < 3
1 $in {1, 2}
$is_set(R)
$p(2)
```

Atomic fact verification is where most proof obligations finally close.

#### 1. Check Well-Definedness

Litex first checks that the objects in the fact make sense. The most common question is whether each function is applied inside its declared domain: if `f` is a function on `R`, then a fact about `f(a)` needs `a` to be usable as a real-number argument.

The same idea appears for set domains, tuple projections, indexed objects, and other object forms.

#### 2. Try Builtin Rules

The main idea is pattern matching. If the fact uses a builtin predicate together with builtin objects, and the whole fact matches a pattern Litex knows, then that kind of fact can be closed automatically.

Typical examples:

```litex
2 + 3 = 5
```

This matches a numeric equality pattern: both sides can be calculated and compared.

```litex
1 $in {1, 2}
```

This matches a membership pattern: an element is checked against an enumerated set.

```litex
$is_finite_set({1, 2})
```

This matches a set predicate pattern: an enumerated set is recognized as a set object.

Builtin rules are not one mysterious tactic. They are many small mathematical patterns for equality, order, membership, sets, tuples, functions, arithmetic, and related standard objects.

#### 3. Try Known Facts

If builtin rules do not close the goal, Litex checks known atomic facts with the same predicate and the same truth value. The arguments do not have to be written with exactly the same text: they may match through known equalities.

For example, suppose these facts are already known:

```text
$p(a, b)
a = a2
b = b2
```

Then this goal can be accepted from the known fact:

```text
$p(a2, b2)
```

Internally, Litex looks up known facts with predicate `$p`, then checks whether each goal argument is equal to the corresponding known argument.

```litex
abstract_prop p(x, y)
forall a, b, a2, b2 set:
    a = a2
    b = b2
    $p(a, b)
    =>:
        $p(a2, b2)
```

#### 4. Try Known `forall` Facts

If direct known facts do not close the goal, Litex searches applicable universal facts. The rough process is:

1. Find known `forall` facts whose conclusion has the same predicate shape as the current goal.
2. Match the current goal's arguments against the `forall` conclusion and build a substitution for the universal parameters.
3. Substitute those parameters into the `forall` assumptions.
4. Check that the substituted assumptions are already known or can be verified.

Object matching is structural. If the `forall` conclusion has a parameter such as `x`, that parameter may bind to the object in the goal. If the conclusion has a structured object such as `f(x)`, `x + 1`, or `(x, y)`, Litex matches the outer shape first, then recursively matches the inner objects.

```text
know forall x R:
    $p(x)

goal:
    $p(2)

match:
    x -> 2
```

```text
know forall x R:
    $p(x + 1)

goal:
    $p(2 + 1)

match:
    x -> 2
```

```text
know forall x, y R:
    $p((x, y))

goal:
    $p((2, 3))

match:
    x -> 2, y -> 3
```

The substitutions are merged as matching goes deeper. If the same universal parameter appears twice, both appearances must match the same object:

```text
know forall x R:
    $p(x, x)

goal:
    $p(2, 2)

match:
    x -> 2
```

```text
know forall x R:
    $p(x, x)

goal:
    $p(2, 3)

match:
    fail

reason:
    x cannot be both 2 and 3
```

Litex also simplifies many common matching steps for you. If the `forall` conclusion has a parameter plus, minus, times, or divided by a number, and the goal gives a single object instead of the same written shape, Litex can move that number to the other side of the match.

```text
know forall x R:
    $p(x + 1)

goal:
    $p(y)

match:
    x -> y - 1
```

```text
know forall x R:
    $p(x * 2)

goal:
    $p(y)

match:
    x -> y / 2
```

The practical lesson is simple: the more similar your goal looks to a known fact or a known `forall` conclusion, the easier it is for Litex to verify it automatically. If the shapes are too different, you usually need to write intermediate facts that gradually rewrite the goal into a familiar shape.

`forall` is the foundation for proving facts beyond builtin rules. A known `forall` fact is like knowing infinitely many facts at once: once Litex finds objects that satisfy the parameter conditions, it can substitute those objects into the `forall` conclusion and obtain the corresponding concrete fact. Builtin rules give Litex a fixed base of mathematical reasoning; `forall` lets users keep generating new facts from their own definitions and theorems.

> The result of a factual statement is either **true** or **unknown**. `unknown` does not mean the statement is false. It means these verification routes did not find enough information. Usually the proof needs a smaller intermediate fact: an equality, a membership fact, a domain condition, a nonzero denominator, or a lemma that should be stated before the current line.

---

### Larger Facts

Larger factual statements do not introduce a completely separate proof engine. They organize smaller checks and eventually reduce to atomic facts or other smaller factual statements.

For a reference list of fact shapes, see [Factual Statements](https://litexlang.com/doc/Manual#factual-statements).

#### Conjunction

```litex
1 = 1 and 2 < 3
```

A conjunction succeeds when each part succeeds. Each part is checked as its own fact.

#### Chain

```litex
0 < 1 < 2
```

A chain is shorthand for adjacent comparisons or equalities. Litex checks the pieces and may record useful transitive consequences.

#### Disjunction

```litex
1 = 2 or 1 = 1
```

Litex first checks that every branch is well-defined. Then it tries builtin rules for common exhaustive splits. If no builtin split applies, Litex checks the branches one by one. If any branch can be verified by the usual fact-verification process, the whole `or` fact is true.

If no branch is directly verified, Litex tries to match the whole `or` fact against known `or` facts, using known equal objects when comparing the arguments. Finally, it can also use known `forall` facts whose conclusion is an `or` fact.

```text
goal:
    1 = 2 or 1 = 1

reason:
    the second branch can be verified
```

```text
goal:
    x < 0 or 0 <= x

reason:
    builtin rule
```

```text
known:
    a = 0 or a > 0
    x = a

goal:
    x = 0 or x > 0

reason:
    the whole or fact matches the known or fact using x = a
```

```text
know forall x R:
    x < 0 or 0 <= x

goal:
    a < 0 or 0 <= a

match:
    x -> a
```

#### Existential Facts

```litex
exist x R st { x = 1 }
```

Existential fact verification follows the same general routes. First, Litex checks that the parameter domains and body facts are well-defined. Then it tries to verify the existential fact by matching known information.

Builtin rules usually appear when Litex checks instantiated body facts:

```text
goal:
    exist x R st { x = 1 }

witness:
    x -> 1

body after substitution:
    1 = 1

reason:
    builtin rule
```

Known existential facts can be reused. Parameter names do not matter because Litex normalizes the body by renaming existential parameters:

```text
known:
    exist y R st { y = 1 }

goal:
    exist x R st { x = 1 }

reason:
    same normalized existential body
```

Known `forall` facts can also prove existential facts when their conclusion is an existential fact:

```text
know forall A Set:
    exist x A st { x $in A }

goal:
    exist x N st { x $in N }

match:
    A -> N
```

There is also a common user-facing path: the user can give a witness explicitly. Litex verifies that by substitution. It temporarily treats the existential parameter as equal to the witness object, runs the proof block, substitutes the witness into the body facts, and verifies those instantiated facts. Those body facts then reduce to the usual atomic fact, conjunction, chain, disjunction, or nested existential verification.

#### Universal Facts

```litex
forall x R:
    x = x
```

A universal fact is checked in a local temporary context. Litex introduces the parameters, stores their domain facts as known facts, assumes the premise facts in that local context, and then verifies the conclusion facts there. Those conclusion facts again reduce to atomic facts or smaller factual statements.

```text
forall x R, y Z:
    $p(x, y)
    =>:
        $q(x, y)
```

For this example, Litex opens a local environment, declares `x $in R` and `y $in Z`, stores `$p(x, y)` as a known fact in that environment, and then verifies `$q(x, y)` inside the same environment.

Litex also has universal facts with `<=>:`. They are checked by reducing the equivalence to two ordinary `forall` facts:

```text
forall x R:
    $t(x)
    =>:
        $p(x)
    <=>:
        $q(x)
```

Litex verifies both directions:

```text
forall x R:
    $t(x)
    $p(x)
    =>:
        $q(x)
```

```text
forall x R:
    $t(x)
    $q(x)
    =>:
        $p(x)
```

So `forall` with `<=>:` is still the same local-environment process. Litex opens a temporary context, assumes one side, verifies the other side, then checks the reverse direction in another temporary context.

> Complex facts explain how to break the proof into sub-goals. Atomic facts are where most verification actually closes.

---

### Why The Builtin Layer Is Large

Litex includes many basic mathematical objects and rules because ordinary proofs use many small background facts. Numbers, sets, membership, functions, tuples, products, order, equality, finite displays, and positivity conditions constantly interact.

Each individual builtin rule is meant to be simple:

```litex
1 $in {1, 2}
2 + 3 = 5
0 <= 2
$is_set(R)
```

The size comes from combinations. A proof about a function may need arithmetic on its output, membership in its domain, tuple projections, set inclusion, and equality substitution. If every one of those steps had to be rebuilt as a user theorem, proofs would be dominated by bookkeeping.

The builtin layer is Litex's shared mathematical background. User-defined `prop`s and `forall` theorems add domain-specific ideas on top of that background, while the language handles the common low-level facts of basic mathematics.

---

### Read The Output Message

When Litex verifies a file, read the output message. It tells you how each fact was proved.

For example, a successful fact result may show:

```litex
let a, x R:
    a = 0 or a > 0
    x = a

x = 0 or x > 0
```

```text

{
  "result": "success",
  "type": "DefLetStmt",
  "line": 1,
  "stmt": "let a, x R:\n    a = 0 or a > 0\n    x = a",
  "infer_facts": [
    "a $in R",
    "x $in R",
    "a = 0 or a > 0",
    "x = a"
  ],
  "inside_results": []
}

{
  "result": "success",
  "type": "Fact",
  "line": 5,
  "stmt": "x = 0 or x > 0",
  "verified_by":   {
    "type": "known_fact",
    "line": 2,
    "source": "entry",
    "cited_fact": "a = 0 or a > 0"
  },
  "infer_facts": [],
  "inside_results": []
}
```

This means the goal `x = 0 or x > 0` was not proved by a fresh builtin calculation. It was proved by matching a known fact, namely `a = 0 or a > 0`. These messages are useful for learning Litex's proof process: they show whether a fact closed by builtin rules, by a known fact, by a known `forall`, or by another recorded verification route.

---

## Builtin Verification Rules

_There is nothing more deceptive than an obvious fact._

_– Sherlock Holmes_

Builtin verification rules are the mathematical patterns Litex can use to close a goal while checking a fact. They are part of the verification phase, before a fact is stored.

The main idea is simple: if a goal uses builtin predicates and builtin objects, and it matches a mathematical pattern Litex knows, Litex can close it without asking the user to write a separate theorem.

For the full flow around goals, storage, and inference, see [Proof Process](https://litexlang.com/doc/Manual#proof-process).

---

### How To Read This Page

This page is not something to memorize. It is a map of common builtin patterns, and you can read it casually when you want to know what Litex can close automatically.

Most examples are real `litex` snippets. They are meant to show the shape of facts Litex can verify automatically. The checker may use several smaller rules internally, but the user-facing experience is that the fact just closes.

There are many entries here because basic mathematical concepts have many simple pairwise relationships. Each relationship is usually easy, but the total number of combinations is large. One of Litex's main design choices is to build in many of these simple-but-numerous relationships. The result is that user code can stay closer to everyday mathematical writing without giving up runtime speed.

When a rule does not apply, the usual fix is to write an intermediate fact that makes the goal look more like one of these patterns.

---

### Equality Rules

Equality goals are mainly handled by evaluation, normalization, structural matching, and standard algebraic identities.

#### Numeric Evaluation

Pure numeric goals are reduced and compared.

```litex
2 + 3 * 4 = 14
```

Integer remainder with concrete operands is evaluated directly.

```litex
4 % 2 = 0
```

Rational equalities can close by the rational pipeline, which is morally cross-multiplication under valid denominators.

```litex
2 / 3 = 4 / 6
```

#### Algebraic Normalization

Equivalent polynomial expressions over ordinary number domains can normalize to the same form.

```litex
forall a, b R:
    (a + b)^2 = a^2 + a*b + b^2 + b*a
```

Same-head expressions can be proved equal when their corresponding arguments are equal.

```litex
forall x, y R:
    x = y
    =>:
        (x + 1) * (x + 1) = (y + 1) * (y + 1)
```

The same structural idea applies to many composite objects: matrices, `max`, `min`, set operations, tuples, and other builtin object heads.

#### Known Numeric Values

After a name is known to equal a concrete number, Litex can resolve that name when checking later equalities.

```litex
have a R = 2
a ^ 2 = 4
```

This is why facts like `x = 2` are so useful: they make later expressions involving `x` calculable.

#### Functions And Families

For a named function introduced by `have fn`, Litex can instantiate the function body at the given arguments.

```litex
have fn f(x R) R = x + 1
f(2) = 3
```

Anonymous functions behave the same way: applying the function substitutes the argument into the body.

```litex
'R(x){x + 1}(2) = 3
```

A parameterized `family` expands to the object it defines when instantiated.

```litex
prove:
    family p(a set) = fn(x a) a
    \p(R) = fn(x R) R
```

#### Absolute Value

Litex knows the usual absolute-value cases.

```litex
forall x R:
    0 <= x
    =>:
        abs(x) = x
```

```litex
forall x R:
    x <= 0
    =>:
        abs(x) = -x
```

It also knows common algebraic identities involving `abs`.

```litex
forall x, y R:
    abs(x * y) = abs(x) * abs(y)
```

```litex
forall x R:
    x^4 = abs(x)^4
```

If `abs(x) = 0` is known, Litex can conclude `x = 0`.

```litex
forall x R:
    abs(x) = 0
    =>:
        x = 0
```

#### Powers

Exponent one simplifies to the base.

```litex
forall a R:
    a^1 = a
```

Positive integer exponents can use the usual exponent-addition law.

```litex
forall a R, m, n N_pos:
    a^(m + n) = a^m * a^n
```

If a positive literal power is zero, Litex can reduce the goal to the base being zero.

```litex
prove:
    forall a R:
        a = 0
        =>:
            a ^ 3 = 0
```

A difference against literal zero can close when the two sides are known equal.

```litex
prove:
    have x R = 5
    x - x = 0
```

#### Logarithms

Logarithm rules follow the standard inverse and algebra laws, with well-definedness and domain conditions checked first.

```litex
forall a, b R_pos:
    a != 1
    =>:
        log(a, a^b) = b
```

```litex
forall a, b, c R_pos:
    a != 1
    a^b != 1
    =>:
        log(a^b, c) = log(a, c) / b
```

```litex
forall a, x, b R_pos:
    a != 1
    =>:
        log(a, x^b) = b * log(a, x)
```

```litex
forall a, x, y R_pos:
    a != 1
    =>:
        log(a, x * y) = log(a, x) + log(a, y)
```

```litex
forall a, x, y R_pos:
    a != 1
    =>:
        log(a, x / y) = log(a, x) - log(a, y)
```

```litex
forall a, b R_pos, c R:
    a != 1
    a^c = b
    =>:
        log(a, b) = c
```

#### Finite Sums And Products

Litex has builtin rules for common finite `sum` and `product` shapes: splitting summands, concatenating adjacent ranges, peeling the last term, tiling a range, reindexing by a constant shift, and summing a constant body.

```litex
sum(1, 3, '(x Z) Z {x + x}) = sum(1, 3, '(x Z) Z {x}) + sum(1, 3, '(x Z) Z {x})
```

```litex
sum(1, 3, '(x Z) Z {x + x}) + sum(4, 6, '(x Z) Z {x + x}) = sum(1, 6, '(x Z) Z {x + x})
```

```litex
sum(1, 3, '(x Z) Z {x}) = sum(1, 2, '(x Z) Z {x}) + '(x Z) Z {x}(3)
```

```litex
product(1, 3, '(x Z) Z {x}) = product(1, 2, '(x Z) Z {x}) * '(x Z) Z {x}(3)
```

```litex
sum(1, 10, '(x Z) Z {x}) = sum(1, 3, '(x Z) Z {x}) + sum(4, 8, '(x Z) Z {x}) + sum(9, 10, '(x Z) Z {x})
```

```litex
product(1, 10, '(x Z) Z {x}) = product(1, 3, '(x Z) Z {x}) * product(4, 8, '(x Z) Z {x}) * product(9, 10, '(x Z) Z {x})
```

```litex
sum(1, 3, '(x Z) Z {x}) = sum(2, 4, '(x Z) Z {x - 1})
```

```litex
have c Z
sum(1, 3, '(x Z) Z {c}) = ((3 - 1) + 1) * c
```

#### Modular Arithmetic

Concrete `%` expressions are evaluated when possible. Litex also knows common congruence patterns.

```litex
forall m Z:
    m != 0
    =>:
        0 % m = 0
```

```litex
forall x1, x2, y1, y2 Z, m N_pos:
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 + y1) % m = (x1 % m + y1 % m) % m = (x2 % m + y2 % m) % m = (x2 + y2) % m
```

```litex
forall x1, x2, y1, y2, m Z:
    m != 0
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 - y1) % m = (x2 - y2) % m
```

```litex
forall x1, x2, y1, y2, m Z:
    m != 0
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 * y1) % m = (x2 * y2) % m
```

Taking `% m` twice with the same `m` is redundant.

```litex
prove:
    (5 % 7) % 7 = 5 % 7
```

---

### Order And Comparison Rules

Order goals use sign reasoning, monotonicity, standard number-set facts, and fraction comparison.

#### Numeric Comparisons

Concrete numeric inequalities are evaluated directly.

```litex
1 < 2
```

```litex
2 <= 2
```

When both sides are explicit fractions with nonzero denominators, Litex may compare by clearing denominators.

```litex
prove:
    1 / 2 < 3 / 4
```

#### Bounds From Number Sets

Litex knows basic order facts about `N` and `N_pos`.

```litex
forall n N_pos:
    1 <= n
```

```litex
forall n N:
    0 <= n
```

```litex
forall x N:
    x != 0
    =>:
        1 <= x
```

```litex
forall x N:
    1 <= x
    =>:
        x != 0
```

#### Sums, Products, Quotients, And Powers

Nonnegative or positive parts can make a larger expression nonnegative or positive.

```litex
forall a, b R:
    0 <= a
    0 <= b
    =>:
        0 <= a + b
```

```litex
let a, b, c R:
    0 <= a
    0 <= b
    0 <= c

0 <= a + b + c
```

```litex
forall a, b R:
    0 < a
    0 <= b
    =>:
        0 < a + b
```

```litex
forall a, b, c R:
    a < b
    0 <= c
    =>:
        a < b + c
```

```litex
0 <= 3 * 2
```

```litex
0 <= 3 / 2
```

```litex
0 <= (-2) ^ 2
```

```litex
forall a R:
    0 <= a ^ 2
```

```litex
0 < 2 ^ 3
```

#### Combining Inequalities

Litex knows standard monotonicity patterns for addition, subtraction, multiplication by a nonnegative value, and division by a positive value.

```litex
forall a, b, c, d R:
    a <= b
    c <= d
    =>:
        a + c <= b + d
```

```litex
forall a, b, c, d R:
    a <= b
    c <= d
    =>:
        a - d <= b - c
```

```litex
forall a, b R:
    0 <= a
    1 <= b
    =>:
        a <= b * a
```

```litex
prove:
    have k R = 2
    have a R = 1
    have b R = 3
    0 <= k
    a <= b
    k * a <= k * b
```

```litex
prove:
    have a R = 2
    have b R = 4
    have c R = 3
    0 < c
    a < b
    a / c < b / c
```

#### Sign Flips And Absolute Value

Multiplying by `-1` flips the sign in the usual way.

```litex
forall x R:
    x <= 0
    =>:
        0 <= -1 * x
```

Litex also knows the standard order properties of `abs`.

```litex
forall x R:
    x <= abs(x)
```

```litex
forall x R:
    -x <= abs(x)
```

```litex
forall x R:
    0 <= abs(x)
```

```litex
forall x, b R:
    x <= b
    -x <= b
    =>:
        abs(x) <= b
```

```litex
forall x, y R:
    abs(x + y) <= abs(x) + abs(y)
```

```litex
forall x, y R:
    abs(x) - abs(y) <= abs(x + y)
```

#### Disequality

Disequalities such as `!=` can close when numeric or ordering information rules out equality.

```litex
2 != 3
```

---

### Membership Rules

Membership goals are checked by evaluating the object and recognizing standard set shapes.

#### Standard Number Sets

Concrete literals and many arithmetic combinations of literals can be checked against standard number sets.

```litex
1 $in N_pos
```

```litex
1 + 1 $in N
```

Negated membership in a standard set can close for concrete numeric values.

```litex
prove:
    not (-1) $in N
```

#### Numeric Cones And `max` / `min`

If `max(a,b)` or `min(a,b)` is asserted inside a standard one-sided number cone, Litex may close the goal when both operands are already known to lie in that same cone.

```litex
prove:
    max(2, 3) $in R_pos
```

#### Finite Sums And Products

A finite `sum` or `product` over an integer range is treated as a real once the indexed expression is well-defined.

```litex
prove:
    sum(1, 3, '(x Z) Z {x}) $in R
```

---

### Set Inclusion Rules

Subset goals are treated as universal membership: every element of the left set must lie in the right set.

```litex
{1} $subset {1, 2}
```

Superset and negated subset or superset claims are related to the same membership idea. When a direct subset statement is clumsy, write the universal membership fact explicitly as in an ordinary proof.

---

### Type Predicate Rules

Type predicates recognize standard object shapes.

```litex
$is_set({1, 2})
```

Nonempty enumerated sets, standard sets such as `R`, integer closed ranges with valid endpoints, Cartesian products with nonempty factors, nonempty function spaces, and similar shapes can be recognized as nonempty.

```litex
$is_nonempty_set({1})
```

```litex
prove:
    $is_nonempty_set(closed_range(0, 2))
```

```litex
prove:
    $is_nonempty_set(cart(R_pos, R_pos))
```

An empty enumeration proves negated non-emptiness.

```litex
prove:
    not $is_nonempty_set({})
```

Finite-set syntax is recognized directly.

```litex
$is_finite_set({1, 2})
```

Tuple and Cartesian-product shapes are recognized structurally.

```litex
$is_tuple((2, 3))
```

```litex
$is_cart(cart(R, Q))
```

---

### Function Equality Rules

Function equality rules reduce function equality to pointwise equality.

#### Equality On A Set

`$fn_eq_in(f, g, S)` means that `f` and `g` agree on every input in `S`. The checker reduces the goal to the corresponding pointwise facts.

```litex
have fn f(x R) R = x
have fn g(x R) R = x

forall x R:
    f(x) = x = g(x)

$fn_eq_in(f, g, R)
```

Anonymous function heads can be compared the same way when they denote the same map on the set.

```litex
$fn_eq_in('R(x){x}, 'R(y){y}, R)
```

#### Equality From Function Type

`$fn_eq(f, g)` is for values whose function type is given by the same `fn(...)` or `have fn` specification on both sides. After checking that the type data matches, the goal reduces to a parameterized proof that `f` and `g` agree on every argument tuple.

```litex
$fn_eq('R(x){x}, 'R(y){y})
```

```litex
have fn f(x R) R = x
have fn g(x R) R = x
forall x R:
    f(x) = x = g(x)
$fn_eq(f, g)
```

Two function-set values written with the same `fn` parameter list and body-shaped data can be proved equal when each side implies the other as a type.

---

### Practical Advice

Builtin verification works best when your goal is written in a familiar shape. If a mathematically true statement does not close, try adding a smaller intermediate fact: an equality, a sign condition, a membership fact, a nonzero denominator, or a pointwise fact for function equality.

Also read the output message. It often tells you whether a fact was closed by builtin rules, a known fact, or a known `forall`.

---

## Inference

_The more I think about language, the more it amazes me that people ever understand each other at all._

_- Kurt Gödel_

Verification answers the question: **can this fact be proved now?**

Inference happens after that. Once a fact is verified or introduced by `know`, Litex stores it in the current environment and may derive more facts from it. Those derived facts become ordinary known information for later proof steps.

The main purpose is usability. Inference saves the user from manually writing the obvious next facts again and again.

This is different from [Builtin Verification Rules](https://litexlang.com/doc/Manual#builtin-verification-rules). Verification rules close the current goal. Inference adds useful consequences after a fact has already been accepted. For the full loop from verification to storage and inference, see [Proof Process](https://litexlang.com/doc/Manual#proof-process).

---

### The Mental Model

Think of inference as automatic bookkeeping.

If you tell Litex:

```text
x $in N_pos
```

Litex remembers not only that membership fact, but also useful consequences such as:

```text
0 < x
```

If you tell Litex:

```text
A $subset B
```

Litex can remember the universal membership consequence:

```text
forall x A:
    x $in B
```

The point is not to replace proof. The point is to keep basic mathematical consequences available so later facts can match known information more naturally.

---

### Which Facts Trigger Inference

Most inference rules are triggered by **atomic facts**: equalities, memberships, comparisons, predicates, subset facts, and similar small claims.

Some larger fact shapes have special inference behavior:

- `exist!` adds a uniqueness statement: any two witnesses satisfying the body must agree.
- `not exist` adds the usual universal De Morgan form.
- `not forall` adds an existential counterexample.
- equality chains add the equalities forced by transitivity, and those equalities then infer as usual.

Some larger facts do **not** trigger this extra pass by themselves:

- `and`
- `or`
- outermost `forall`, including `forall` with `<=>:`

Their atomic pieces may still trigger inference when those pieces are assumed, proved, or stored separately.

---

### Equality Inference

Equality inference is mainly about remembering equivalent forms and structural information.

#### Difference Equals Zero

If one side is `0` and the other side is a difference `u - v`, inference adds `u = v`.

```text
known:
    a - b = 0

inferred:
    a = b
```

#### Concrete Numeric Values

If one side simplifies to a concrete number, Litex treats the other side as known to equal that number for substitution and numeric reasoning.

```text
known:
    x = 2

later goal:
    x + 1 = 3

reason:
    x can be resolved to 2
```

This may not always appear as a separate displayed `infer_facts` line. Sometimes it is stored as side information used later by resolution.

#### Simple Linear Equations

If an equality has a simple linear form and one side is a concrete number, inference may treat the main unknown as fixed to that number, in the same way as the numeric-value case.

```text
known:
    x + 1 = 3

remembered:
    x is fixed to 2
```

#### Tuples And Cartesian Products

If one side is a tuple and the other side is not, Litex remembers tuple information about the other object.

```text
known:
    t = (a, b)

inferred:
    $is_tuple(t)
```

If one side is a literal Cartesian product such as `cart(R, Q)`, Litex remembers that the other object is a Cartesian product, along with its number of factors and related metadata.

```text
known:
    d = cart(R, Q)

inferred:
    $is_cart(d)
```

#### Displayed Sequences, Matrices, And Functions

If one side is a finite sequence literal or a matrix literal and the other side is a name, Litex remembers that the name has that sequence or matrix shape.

If one side is an anonymous function and the other side is a name, Litex remembers the function argument list and, when present, the defining equation.

These rules are mostly bookkeeping rules. They help later object checks and equality checks avoid repeating shape information.

#### Predicate Definitions

For a user-defined `prop` with `<=>:` clauses, once `$P(args)` is known, inference instantiates the corresponding definition facts by plugging in those arguments.

```text
prop unit_x(x R):
    forall x R:
        =>:
            x = 1
        <=>:
            x + 0 = 1

known:
    $unit_x(a)

available through inference:
    a + 0 = 1
```

What gets inferred depends on how the predicate is defined.

---

### Membership Inference

Membership facts are one of the most common sources of inferred information.

#### Number Sets

Membership in more specific number sets gives sign or nonzero information.

```text
known:
    k $in N

inferred:
    0 <= k
```

```text
known:
    x $in R_pos

inferred:
    0 < x
```

```text
known:
    x $in R_neg

inferred:
    x < 0
```

```text
known:
    x $in R_nz

inferred:
    x != 0
```

Plain membership in `Z`, `Q`, or `R` alone does not add a sign fact.

#### Finite Enumerations

Membership in an enumerated finite set becomes a finite disjunction.

```text
known:
    a $in {1, 2}

inferred:
    a = 1 or a = 2
```

#### Products And Tuples

Membership in `cart(...)` adds tuple information and aligns product-set bookkeeping.

```text
known:
    u $in cart(R, R)

inferred:
    $is_tuple(u)
```

#### Ranges

Membership in a half-open integer range gives integer membership and two-sided bounds.

```text
known:
    i $in range(2, 6)

inferred:
    i $in Z
    2 <= i
    i < 6
```

Membership in a closed range gives closed bounds.

```text
known:
    i $in closed_range(1, 3)

inferred:
    i $in Z
    1 <= i
    i <= 3
```

#### Set Comprehensions

Membership in a set comprehension adds membership in the base set and each filter condition with the bound variable replaced by the element.

```text
known:
    x $in { y R: 0 <= y }

inferred:
    x $in R
    0 <= x
```

#### Function-Like Sets And Families

Membership in `fn(...)` records function-space information for suitable function heads, so later goals can use the expected domain and codomain.

Membership in `finite_seq(...)`, `seq(...)`, and `matrix(...)` is handled similarly because these objects are read as function-like types.

For membership in a `family` instance such as `\name(...)`, Litex expands the family to the set it denotes, then applies the usual membership inference rules to that expanded set.

---

### Subset And Superset

From `A $subset B`, Litex infers that every element of `A` is also in `B`.

```litex
prove:
    let A, B set:
        A $subset B
    forall x A:
        x $in B
```

From `A $superset B`, Litex infers that every element of `B` is also in `A`.

```litex
prove:
    let A, B set:
        A $superset B
    forall x B:
        x $in A
```

Inside a `forall ... =>:` block, the conclusion cannot be another raw `forall`. In examples like these, use `let` to store the subset or superset fact, then write the inferred universal membership fact separately.

---

### Order Inference

Order inference mainly turns a comparison with a concrete constant into a simpler sign fact.

If exactly one side of an inequality is a numeric constant, Litex may compare the other side with `0`.

```text
known:
    2 <= a

inferred:
    0 < a
```

```text
known:
    -1 >= b

inferred:
    b <= 0
```

When the right-hand side is `0` and the left-hand side is not already `(-1) * u`, Litex may flip the inequality into a statement about `-1` times the left-hand side.

```text
known:
    x < 0

inferred:
    -1 * x >= 0
```

There is no matching automatic rule when `0` is on the left.

---

### Function Restriction

For `$restrict_fn_in`, inference narrows the recorded function-space information to the more specific function type you gave. It does not need to restate the whole function definition.

```text
known:
    $restrict_fn_in(f, smaller_fn_type)

remembered:
    f can be used with the smaller function type
```

---

### Facts With No Extra Inference

Some builtin atoms are left as they are for this pass. Examples include negated comparisons, `$is_set`, `not $restrict_fn_in`, and similar facts.

They can still be used in proofs. Inference simply does not unfold them further here.

---

### Read The Output Message

When Litex runs, the output may include `infer_facts` or other recorded information. Read that message when you want to understand what inference added after a fact was stored.

If a later fact succeeds unexpectedly, the reason is often that an earlier fact inferred useful information such as a sign condition, a membership consequence, a tuple shape, or a numeric substitution.
