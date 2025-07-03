# Litex for Curious Lean Users

## Technical Comparison

**skip this section if you are in hurry**

Technically, the difference between Litex and Lean is that Litex is a read-only Turing machine, while Lean is a full Turing machine. The complexity of Lean stems from its dual purpose: it aims to be both a programming language and a reasoning verifier. This is similar to how Newton couldn't have invented calculus if he had to learn theories that would be developed three centuries later. By sacrificing Turing completeness, Litex eliminates variables, control flow, and execution semantics - concepts that are foreign to pure mathematics. This design choice, similar to how SQL specializes in database operations, allows Litex to focus on everyday mathematics. Since even a 10-year-old can understand and reason about mathematics intuitively, Litex is designed to align as closely as possible with everyday mathematical thinking.

You can think of Litex as a Lean Alternative for Human-Friendly Mathematical Formalization.

## Examples

Mathematics is the art of deriving new facts from established ones. To illustrate, consider a classical syllogism proposed by Aristotle in his Prior Analytics, which formalizes deductive reasoning as follows:

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>obj Human set</code> <br><br>
      <code>prop self_aware(x Human)</code> <br><br>      <code>know forall x Human:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;$self_aware(x)</code> <br> <br>
      <code>obj Bob Human</code> <br> <br>
      <code>$self_aware(Bob)</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>def Human := Type</code> <br><br>
      <code>def self_aware (x : Human) : Prop := true</code> <br><br>
      <code>axiom self_aware_all :</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;∀ (x : Human), self_aware x</code> <br><br>
      <code>def Bob : Human := Human</code> <br><br>
      <code>example : self_aware Bob := self_aware_all Bob</code>
    </td>
  </tr>
</table>

Consider `Human` as the set of all humans. Using `know`, we establish the fact without the need to be verified by other facts: all humans are self-aware. Since Bob is in the set of `Human`, "Bob is self-aware" is inherently true.

Notice how Litex requires much less typing than Lean4 even in this simple example. An obvious advantage of Litex is that it reduces typing by eliminating the need to name or recall individual facts. When writing done factual expressions for verification, Litex automatically searches for relevant facts, akin to a regular expression search in a large database. For instance, instead of naming an axiom like "axiom self_aware_all," you simply write "know ...". This approach significantly reduces the cognitive load and enhances efficiency in handling complex logical structures.

Although this is a simple example, it has already taught us how ANY mathematical facts are derived from known facts. Just as Lego lets you assemble complex structures from simple pieces, Litex lets you build math from minimal (with just 8 main keywords: forall, exist, not, or, fn, prop, obj, set and several other auxiliary keywords), reusable parts -— no unnecessary complexity, just pure flexibility.

Also notice Litex adopts a mixture of Python and GoLang's syntax, making it easy to pick up for users who has some programming experience.

Another example is the definition of algorithm. In mathematics, an algorithm is a computational method that can be precisely defined as a quadruple (Q, I, S, f), where:
- Q is a set representing all possible states of computation
- I is a subset of Q representing valid inputs
- S is a subset of Q representing valid outputs
- f is a function from Q to Q that defines the computational rule

The computation proceeds by repeatedly applying f to an input x in I, generating a sequence x₀, x₁, x₂, ... where x₀ = x and xₖ₊₁ = f(xₖ). An algorithm must terminate in finitely many steps for any valid input, producing an output in S. This formal definition ensures that algorithms are well-defined mathematical objects that can be rigorously analyzed and verified.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>fn comp_seq(Q set, f fn(Q)Q) fn(Q, N)Q:</code><br>
      <code>&nbsp;&nbsp;forall x Q:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;comp_seq(Q, f)(x,n) = f(comp_seq(Q, f)(x, n-1))</code><br><br>
      <code>exist_prop n N st exist_comp_seq_end(Q set, x Q, f fn(Q,N)Q):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;f(x, n) = f(x, n+1)</code><br><br>
      <code>prop is_algorithm(Q set, I set, f fn(Q)Q):</code><br>
      <code>&nbsp;&nbsp;$subset_of(I, Q)</code><br>
      <code>&nbsp;&nbsp;iff:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall x I:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$exist_comp_seq_end(Q, x, comp_seq(Q, f))</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>structure ComputationalMethod where</code><br>
      <code>&nbsp;&nbsp;Q : Type</code><br>
      <code>&nbsp;&nbsp;I : Set Q</code><br>
      <code>&nbsp;&nbsp;S : Set Q</code><br>
      <code>&nbsp;&nbsp;f : Q → Q</code><br>
      <code>&nbsp;&nbsp;f_fixed : ∀ q ∈ S, f q = q</code><br><br>
      <code>namespace ComputationalMethod</code><br><br>
      <code>def comp_seq (cm : ComputationalMethod) (x : cm.Q) : ℕ → cm.Q</code><br>
      <code>&nbsp;&nbsp;| 0 => x</code><br>
      <code>&nbsp;&nbsp;| n + 1 => cm.f (comp_seq x n)</code><br><br>
      <code>def TerminatesIn (cm : ComputationalMethod) (x : cm.Q) (k : ℕ) : Prop :=</code><br>
      <code>&nbsp;&nbsp;comp_seq cm x k ∈ cm.S ∧</code><br>
      <code>&nbsp;&nbsp;∀ i < k, comp_seq cm x i ∉ cm.S</code><br><br>
      <code>def IsAlgorithm (cm : ComputationalMethod) : Prop :=</code><br>
      <code>&nbsp;&nbsp;∀ x ∈ cm.I, ∃ k, TerminatesIn cm x k</code><br><br>
      <code>end ComputationalMethod</code>
    </td>
  </tr>
</table>

```
fn comp_seq(Q set, f fn(Q)Q) fn(Q, N)Q:
    forall x Q:
        comp_seq(Q, f)(x,n) = f(comp_seq(Q, f)(x, n-1))
```

`comp_seq` defines a function that takes two arguments: a set `Q` and a function `f` from `Q` to `Q`. The function `comp_seq` returns a function from `Q` to `N` that takes two arguments: an element `x` of `Q` and a natural number `n`. The function `comp_seq` returns the `n`-th application of `f` to `x`.

```
exist_prop n N st exist_comp_seq_end(Q set, x Q, f fn(Q,N)Q):
    f(x, n) = f(x, n+1)
```

`exist_prop n N st exist_comp_seq_end(Q set, x Q, f fn(Q,N)Q):` reads: there exists a natural number `n` such that `exist_comp_seq_end(Q, x, f)` is true, and `exist_comp_seq_end(Q, x, f)` is defined as `f(x, n) = f(x, n+1)`.

```
prop is_algorithm(Q set, I set, f fn(Q)Q):
    subset_of(I, Q)
    iff:
        forall x I:
            exist_comp_seq_end(Q, x, comp_seq(Q, f))
```

`is_algorithm` is a proposition that says: when `I` is a subset of `Q`, `$is_algorithm(Q, I, f)` is true if and only if for all `x` in `I`, there exists a natural number `n` such that `f(x, n) = f(x, n+1)`.

Here we can see that Litex achieves remarkable conciseness in formalizing the definition of algorithm - requiring only 10 lines of code while maintaining mathematical clarity. Each statement is self-explanatory and closely mirrors natural mathematical notation. In contrast, Lean 4 requires approximately three times more code to express the same concept. The additional complexity in Lean 4 stems from its need for explicit type definitions, structural elements, and unfamiliar syntax that are not typically encountered in everyday mathematical expressions. This extra complexity creates a steeper learning curve and can distract users from focusing on the core mathematical concepts they're trying to formalize. Litex's approach, by staying closer to conventional mathematical notation, significantly lowers the barrier to entry while maintaining formal strictness.

At the same time, Lean forces to learn these keywords: `structure`, `namespace`, `def`, `end`, `example`, `exact`, `rw`, `simp`, `ring` before starting to formalize math. Sometimes using extra keywords helps users to express more easily, but in most cases, it just makes the code more complex and harder to understand. The user does not know why he needs to learn these keywords in the first place. Lean usually forces you to learn these keywords before you can start to formalize math no matter whether those keywords are truly useful or not.

Next I want to show you how Litex can be used to solve a simple linear equation.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>obj x R, y R:</code><br>
      <code>&nbsp;&nbsp;2 * x + 3 * y = 10</code><br>
      <code>&nbsp;&nbsp;4 * x + 5 * y = 14</code><br><br>
      <code>2 * (2 * x + 3 * y) = 2 * 10</code><br>
      <code>4* x + 6 * y = 2 * 10</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = 2 * 10 - 14</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = y</code><br>
      <code>y = 6</code><br>
      <code>2 * x + 3 * 6 = 10</code><br>
      <code>2 * x + 18 - 18 = 10 - 18</code><br>
      <code>2 * x + 18 - 18 = -8</code><br>
      <code>(2 * x) / 2 = -8 / 2</code><br>
      <code>(2 * x) / 2 = x</code><br>
      <code>x = -4</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>import Mathlib.Tactic</code><br><br>
      <code>example (x y : ℝ) (h₁ : 2 * x + 3 * y = 10) (h₂ : 4 * x + 5 * y = 14) : x = -4 ∧ y = 6 := by</code><br>
      <code>&nbsp;&nbsp;have h₃ : 2 * (2 * x + 3 * y) = 2 * 10 := by rw [h₁]</code><br>
      <code>&nbsp;&nbsp;have h₄ : 4 * x + 6 * y = 20 := by linear_combination 2 * h₁</code><br>
      <code>&nbsp;&nbsp;have h₅ : (4 * x + 6 * y) - (4 * x + 5 * y) = 20 - 14 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [h₄, h₂]</code><br>
      <code>&nbsp;&nbsp;have h₆ : (4 * x + 6 * y) - (4 * x + 5 * y) = y := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;ring</code><br>
      <code>&nbsp;&nbsp;have h₇ : 20 - 14 = 6 := by norm_num</code><br>
      <code>&nbsp;&nbsp;have h₈ : y = 6 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [←h₆, h₅, h₇]</code><br>
      <code>&nbsp;&nbsp;have h₉ : 2 * x + 3 * 6 = 10 := by rw [h₈, h₁]</code><br>
      <code>&nbsp;&nbsp;have h₁₀ : 2 * x + 18 = 10 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [mul_add] at h₉</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;simp at h₉</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;exact h₉</code><br>
      <code>&nbsp;&nbsp;have h₁₁ : 2 * x = -8 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;linear_combination h₁₀ - 18</code><br>
      <code>&nbsp;&nbsp;have h₁₂ : x = -4 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;linear_combination h₁₁ / 2</code><br>
      <code>&nbsp;&nbsp;exact ⟨h₁₂, h₈⟩</code>
    </td>
  </tr>
</table>

**Key Difference in Approach:**  
While Lean 4 can use `linarith` to solve linear equations directly (and Litex will support similar functionality in the future), this example demonstrates how Litex solves equations using basic algebraic rules - just like how children learn math:
- Associative property
- Commutative property  
- Distributive property
- Simple substitution

Because properties of basic operations like addition, multiplication, etc. are built-in, the user do not have to memorize extra rules like `rw`, `simp`, `ring`, `linear_combination`, etc.

**Lean's Complexity vs. Litex's Simplicity:**  
Lean requires memorizing numerous proof-specific commands:
- `rw`, `simp`, `ring`, `linear_combination`, etc.
- Mandatory hypothesis declarations
- `example`/`exact` syntax requirements
- Tactical imports just to prove basic statements

Litex eliminates this complexity entirely. The solution reads exactly like standard mathematical working. No extra commands are needed. Litex does the work for you, making writing and reading Litex code as easy as writing and reading a book.

**Structural Advantage of Litex:**  
Lean forces you to:
1. Declare the conclusion BEFORE proving it
2. Work backwards from the solution

Litex works the natural way:
1. Develop the proof step-by-step
2. State the conclusion AFTER deriving it

This matches human intuition and makes the process far better for both human thinkers and AI models. Lean forces you to write proofs in a very closed-ended way, which is believed to be a huge problem for AI models. Litex is by design open-ended, which could solve this challenge faced by AI models trying to use Lean to solve math problems.

**About Lean's Tactics:**  
While Lean provides tactics like `linarith` for simpler proofs:
1. They fail on complex problems (where Litex's approach scales naturally) because not all problems can be solved by existing tactics.
2. Writing custom tactics requires advanced Lean syntax knowledge
3. The cognitive overhead remains even for elementary problems

Litex will in the future introduce a new feature `prove_algo` to mimic how Lean's tactics work.

Litex maintains intuitive accessibility - even a 10-year-old could follow the solution process, with advanced features coming later to match tactics' power without their complexity.

## Comparison 3: definition of union

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
   <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>fn union(s, s2 set) set:</code> <br>      
      <code>&nbsp;&nbsp;forall x obj:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;or:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x $in s</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x $in s2</code>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;then:</code> <br>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x $in union(s, s2)</code>
        <br>
        <code>know prop union_items_in_at_least_one_of_child_set(x obj, s, s2 set):</code> <br>
        <code>&nbsp;&nbsp;x $in union(s, s2)</code> <br>
        <code>&nbsp;&nbsp;then:</code> <br>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;or:</code> <br>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x $in s</code> <br>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x $in
        <code>&nbsp;&nbsp;obj s, s2 set</code> <br>
        <code>&nbsp;&nbsp;obj x s</code> <br>
        <code>&nbsp;&nbsp;x $in union(s, s2)</code> <br>
        <code>&nbsp;&nbsp;forall s, s2 set, x union(s, s2):</code> <br>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;$union_items_in_at_least_one_of_child_set(x, s, s2)</code> <br>
        <code>claim:</code> <br>
        <code>&nbsp;&nbsp;prop union_with_empty_set_is_itself(x obj, s, s2 set):</code> <br>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;s2 := {}</code> <br>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;x $in union(s, s2)</code> <br>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;then:</code> <br>
        <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x $in s</code>
        <br>
        <code>prove:</code> <br>
        <code>&nbsp;&nbsp;not x $in s2</code> <br>
        <code>&nbsp;&nbsp;$union_items_in_at_least_one_of_child_set(x, s, s2)</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>-- Define a set as a predicate of a type</code> <br>
      <code>def set (α : Type) := α → Prop</code> <br>
      <code>-- The membership relation of a set</code> <br>
      <code>notation x "∈" s => s x</code> <br>
      <code>-- The empty set</code> <br>
      <code>def empty_set {α : Type} : set α := λ _ => False</code> <br>
      <code>-- The union operation of sets</code> <br>
      <code>def union {α : Type} (s1 s2 : set α) : set α := λ x => s1 x ∨ s2 x</code> <br>
      <code>-- The property of union: x ∈ union s1 s2 if and only if x ∈ s1 or x ∈ s2</code> <br>
      <code>theorem union_items_in_either_set {α : Type} (x : α) (s1 s2 : set α) :</code> <br>
      <code>&nbsp;&nbsp;x ∈ union s1 s2 ↔ x ∈ s1 ∨ x ∈ s2</code> <br>
      <code>begin</code> <br>
      <code>&nbsp;&nbsp;refl</code> <br>
      <code>&nbsp;&nbsp;end</code> <br>
      <code>-- Proof: if x ∈ s, then x ∈ union s s2</code> <br>
      <code>example {α : Type} (x : α) (s s2 : set α) (h : x ∈ s) :</code> <br>
      <code>&nbsp;&nbsp;x ∈ union s s2</code> <br>
      <code>begin</code> <br>
      <code>&nbsp;&nbsp;left</code> <br>
      <code>&nbsp;&nbsp;exact h</code> <br>
      <code>&nbsp;&nbsp;end</code> <br>
      <code>-- Proof: the union of a set with the empty set is the original set</code> <br>
      <code>theorem union_with_empty_set_is_itself {α : Type} (x : α) (s : set α) :</code> <br>
      <code>&nbsp;&nbsp;x ∈ union s empty_set ↔ x ∈ s</code> <br>
      <code>begin</code> <br>
      <code>&nbsp;&nbsp;rw union_items_in_either_set</code> <br>
      <code>&nbsp;&nbsp;simp [empty_set]</code> <br>
      <code>&nbsp;&nbsp;end</code> <br>
    </td>
  </tr>

```
# Define a function called union, which takes 2 functions as parameters and return a set as return value
fn union(s, s2 set) set:
    forall x obj:
        or:
            x $in s
            x $in s2
        then:
            x $in union(s, s2)

# Property of union: if an item is in the union of 2 sets, then it is in at least one of the sets
know prop union_items_in_at_least_one_of_child_set(x obj, s, s2 set):
    x $in union(s, s2)    
    then:
        or:
            x $in s
            x $in s2

# Example: union(s, s2) is the union of s and s2
prove:
    obj s, s2 set
    obj x s
    x $in union(s, s2)

    forall s, s2 set, x union(s, s2):
        $union_items_in_at_least_one_of_child_set(x, s, s2)

# Example: union(s, {}) is itself
claim:
    prop union_with_empty_set_is_itself(x obj, s, s2 set):
        s2 := {}
        x $in union(s, s2)
        then:
            x $in s
    prove:
        not x $in s2
        $union_items_in_at_least_one_of_child_set(x, s, s2)
```

```
-- Define a set as a predicate of a type
def set (α : Type) := α → Prop

-- The membership relation of a set
notation x "∈" s => s x

-- The empty set
def empty_set {α : Type} : set α := λ _ => False

-- The union operation of sets
def union {α : Type} (s1 s2 : set α) : set α := λ x => s1 x ∨ s2 x

-- The property of union: x ∈ union s1 s2 if and only if x ∈ s1 or x ∈ s2
theorem union_items_in_either_set {α : Type} (x : α) (s1 s2 : set α) :
  x ∈ union s1 s2 ↔ x ∈ s1 ∨ x ∈ s2 :=
begin
  refl  -- directly from the definition
end

-- Proof: if x ∈ s, then x ∈ union s s2
example {α : Type} (x : α) (s s2 : set α) (h : x ∈ s) :
  x ∈ union s s2 :=
begin
  left,
  exact h
end

-- Proof: the union of a set with the empty set is the original set
theorem union_with_empty_set_is_itself {α : Type} (x : α) (s : set α) :
  x ∈ union s empty_set ↔ x ∈ s :=
begin
  rw union_items_in_either_set,
  simp [empty_set],  -- simplify the disjunction of false
end
```

We can see since Lean 4 is built on top of type theory, when the user wants to define a set, he has to define a type first, and then define a set as a predicate of the type. This is a very foreign concept even to most mathematicians, not to mention ordinary people.

On the other hand, Litex does not need to define a type first. It can directly define a set as a predicate of a type. This is a very simple process. Your proof is very clean and conceptually integral. There is no extra mental brought by the formal language. There is no barrier between your thinking and the formalized math. With a small amount of practice (no more than the effort of learning LaTeX or Python), an ordinary person can be as productive as a professional mathematician when using Litex to formalize math (the only difference between you and a professional mathematician is what you write in Litex, not how fast you write in Litex.). 