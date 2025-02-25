# Litex: A Minimalist Proof Assistant

<div align="center">
<img src="assets/logo.png" alt="The Litex Logo" width="300">
</div>

## About

_That language is an instrument of Human reason, and not merely a medium for the expression of thought._

_–- George Boole_

Litex is a minimalist proof assistant (formal language). Since even children grasp math naturally, a formal language design should exist that's easily understood and used by anyone. The goal of Litex is to invent such a language. The implementation approach leverages a profound understanding of the commonalities and distinctions between programming and mathematics.

Traditional proof assistants lack the fluidity and ease needed to scale formal proofs, while Litex handles the growing complexity of modern mathematics effectively through its clean syntax. Litex is designed to be as intuitive as Python or LaTeX, with a minimal learning curve. Users can trust their common sense to write Litex.

Litex has the potential to greatly impact both mathematics and AI:

- **For Mathematics**: 
  - **For individual researchers**, it provides peace of mind by reducing the risk of subtle errors undermining their proofs. With it, interactive textbooks can be created, enabling learners to study more efficiently and innovate.
  - **For the whole mathematics community**, since Litex ensures correctness, the need for paper reviews is eliminated. This fosters trust and enables large-scale collaboration, akin to a "GitHub for Math", because strangers can trust each other's proofs and collaborate to solve problems.

- **For AI**:
  - **More Formal Data**:
Because Litex is an order of magnitude simpler than traditional proof assistants, LLMs may require far fewer datasets to develop the ability to translate existing mathematics into Litex, accelerating formal data growth. The potential large user community also helps provide high-quality data.

  - **Automated Verification**:
Litex can automatically verify LLM outputs for math problems, providing a reliable way to validate and refine their reasoning. This capability is crucial for improving the accuracy and robustness of LLMs in mathematical tasks.

In short, Litex can transform workflow and collaboration of mathematicians. It boost AI's reasoning with more formal data and a super efficient verifier. The core design principle of Litex is simplicity and user-friendliness.

## Getting Started

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

Let us begin with a quick introduction to Litex. The role of Litex is to serve as a daily tool for users, rather than to demonstrate a certain theory. For the sake of pragmatism, our aim here is to show the essential elements of the language without getting bogged down in details, rules, and exceptions. Please refer to reference manual for more information.

### First Example


<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>type Human</code> <br><br>
      <code>prop self_aware(x Human)</code> <br><br>      <code>know forall x Human:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x is self_aware</code> <br> <br>
      <code>var Bob Human</code> <br> <br>
      <code>Bob is self_aware</code>
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

For now, you don't need to understand everything; you only need to conceptually know what the example is doing. I put both Litex code and Lean4 (another popular proof assistant) code here to clarify fundamentals of Litex. We will refer to this example from time to time.

`Human` is a type representing all humans. Mathematically, you can think of `Human` as the set containing all humans. All humans are set to be `self_aware` by the user as a fact (i.e. true expression) using `know` keyword. `Bob` is `Human`. Therefore, `Bob is self_aware` is a true expression.

This is a classic example of syllogism (三段论), which demonstrates some core features and ideas of Litex very well. Notice Litex significantly reduces the amount of typing required by the user, involves fewer keywords and symbols, and is therefore more intuitive.

### Litex Expressions

There are only two kinds of expressions in Litex: constructive expressions and factual expressions. Factual expressions are used by the user to declare some facts as true. Litex then verifies whether these facts are indeed correct. If they are correct, these new facts are added to the proof environment, where they can be used to verify subsequent facts. Constructive expressions are for introducing new elements in proofs, such as new types, new variables, new functions, or new concepts.

#### Factual Expressions

Every Factual expression of Litex has just four kinds of outcomes: true, false, unknown, error. 

- **True**: Litex confirms your expression based on known facts.

- **False**: Litex disproves your expression based on known facts.

- **Unknown**: Litex cannot find relevant facts to conclude.

- **Error**: Your input is incorrect, e.g., a typing mistake.

This mirrors how Humans think when reading proofs: confirming correctness (true), spotting errors (false), being unsure (unknown), or encountering input issues (error).

Previous formal languages(proof assistants), such as Lean4 and Coq, are still general-purpose languages. They support execution, arithmetic, and control flow, which prevents their syntax from focusing solely on theorem proving and requires them to accommodate other functionalities. This results in highly redundant syntax.

Litex, free from execution constraints, functions like a regex matcher or SQL query processor, validating structured statements against formal rules. Adding unnecessary features would dilute its expressive power, that is why Litex expressions only have four outcomes. Execution in Litex is possible but delegated to plugins, not the language itself.

There are different kinds of factual expressions: specific (instantiated), conditional (begin with keyword `if`) and universal expressions (begin with keyword `forall`):

```plaintext
// Comments are written after "//".

// specific
Bob is self_aware

// conditional
if:
    Bob.age = 10    // conditions
    then:
        Bob is young    // results

// universal
forall x Human, y Human:    // declare variables in the universal expression
    cond:
        x.age < y.age   // conditions
    then:
        $younger(x,y)   // results
```

Different factual expressions have distinct meanings and are processed differently by the Litex interpreter. This means they are verified differently and, when stored in the proof environment, are used in unique ways to prove newly input facts.

When the user input a conditional expression, the interpreter first opens a new proof environment, the interpreter set all conditions to be true and verifies resulting factual expressions. If all results are true, the conditional expression is true.

When the user input a universal expression, the interpreter first opens a new proof environment and declare variables written after the 'forall' keyword in this new environment. In this new environment, the interpreter set all conditions to be true and verifies resulting factual expressions. If all results are true, the universal expression is true. Notice the main difference between the conditional expression and the universal expression is whether new variables are involved.

When the user inputs a specific expression, the interpreter searches the current proof environment for known facts with the same proposition name. These facts may be specific, conditional, or universal. If the given specific fact exactly matches a known specific fact or satisfies a conditional or universal expression, it is considered true. Otherwise, the specific expression remains unknown.

In Lean 4, every fact must have a name, and users must explicitly reference these names to use them in proofs. This forces users to remember even the most trivial facts, often with long and complex names, creating unnecessary burden. Litex, on the other hand, automatically searches all known facts to verify the current input, eliminating the need to manually recall and reference fact names. While users can still name facts if desired, it is no longer mandatory. This approach significantly improves the writing experience and makes Litex code cleaner and more intuitive compared to traditional proof assistants.

When the inverse of input factual expression is true, the interpreter outputs false. When the input does not obey syntax rule of Litex, the interpreter outputs error.

#### Constructive Expressions

Every fact must be associated with some concrete object or entity; it cannot exist independently without being tied to something specific. There are three kinds of entities in Litex: variable(var), function(fn), and proposition(prop). The user must first declare a variable before using it. Any entity has a type.

<!-- TODO: I have not implemented the type of function and prop yet. The major obstacle is: if I view cond as a component of a prop or fn, how to implement this? Or should I just pass undefined f like fun(f fun) and wait till the runtime to check validation of type? I guess f fn wait of doing is every reasonable -->

```plaintext
// declare a type

type Human:
    member:
        var age Natural

// declare a variable

var Bob Human: // variable name is Bob, variable type is Human
    Bob.age = 10 // Age of Bob is known by the user to be 10

// declare a function

// input 2 variables with type Real, output variable with type Real
fn add(a Real, b Real) Real:
    then:
        add(a, b) = add(b, a)   // facts about function add

// declare a proposition

prop younger(a Human, b Human):
    cond:
        a.age < b.age
```
<!-- TODO: Better -->
In Litex, `type` has the following functionalities:

- **As as Set**:
The statement var x type_name means that x has the type type_name. Mathematically, this means x belongs to the set called type_name. For example, `var n Real` means n is a real number, i.e., n is in the set of all real numbers. As in most programming languages, every object has a type. However, the object might not have a specific "value" because, in many cases, it is the type of the variable (not its value) that determines its relationships with other objects. For example, no matter what a positive number equals to, it is larger than 0. Since a variable can belong to multiple sets (e.g. 1 is both a real number and a natural number), a variable can have multiple types.

- **Determine Meaning of Operations**:
Objects of different types support different operations and propositions. For example, when a and b are positive natural numbers, expressions like a^b (multiplying a by itself b times) and a < b are well-defined and meaningful. However, when a and b are matrices, operations like a^b and a < b are not standard notations and may not make sense. Importantly, an object should never be passed to a proposition or function if the parameter types do not match the type of that object. This ensures that operations and functions are applied only in contexts where they are well-defined.

- **Own Members**:
In programming, a type is typically called a "struct" (in C) or a "class" (in C++ or Python). Such technique of organizing code is called "object oriented programming (OOP)". Objects of different types can have different members. For example, a human Bob might have an attribute Bob.age. Additionally, the type itself can have members.

- **implement a concept or extend existing types**:

<!-- function that returns new functions or new propositions are not implemented -->

<!-- TODO: below are not well written -->

Everything in Litex is represented by a symbol(a single word). Variables, Functions, Types, propositions are all represented by a single symbol or composited symbol. Function, variable and proposition are called first-class citizens of Litex, because they can be passed to function/proposition parameters and behave as return value.

In mathematics, a variable is a symbol (often a letter like x,y,z) that represents something that have some factual expressions. Variables are used in factual expressions. 

Functions in Litex are not executed. Instead, they are just composer of other symbols. Function parameter list can receive first-class citizens. Function type list can receive type concept pair. You can bind conditions to parameters that appear in function parameters list. The result of the function output have some properties, which appear in then block.

All specific factual expressions have related proposition name. For example, a = b have related proposition =, a < b have proposition <, red(a) have proposition red, subsetOf(x,y) have related proposition subsetOf. Actually you can view Litex proposition as Functions in mainstream programming languages because the "execution" of a "called proposition" (factual expression) outputs outputs: true, false, error, unknown.

<!-- There is no concept parameter list because you can infinitely iterate over that and If you truly what to bind properties to a concept, you should invent math in Litex and make what you are thinking about in variable and add layer to that variable. -->

<!-- You can make everything a function, because function are just variables that can appear before the () in expressions like f(). If you bind no extra features to that function, e.g. fn f() any. then f works like a variable. -->

```plaintext
concept Euclid_Space S:   // suppose S is a Rn
    type_member:
        var dim Nat // dim is positive natural number
        fn __add__(v1 S, v2 S) Real
    member:
        fn __at__(n Nat) Real: // define @, which means the nth index of the 
            cond:
                n < S.dim
    cond:
        forall v1 S, v2 S:  // define addition of two vectors
            forall k Nat:
                (v1 + v2)@k = v1@k + v2@k

```

In this example, we define a concept called Euclidean Space. Sometimes it is crucial to pass "the type of the type" to a proposition, just like how programmers uses templates to pass parameter types to functions. That is where concept comes into place.

Euclidean space is a set of all finite dimensional spaces. S.dim represents the dimension of the space. Typically we write "Let S is R^{n}, where n can be any natural number", now we just write "S Euclid" and S.dim is automatically reserved for us. Notice how undefined variables "x" or "n" are "hidden" as a member of another symbol here. That is why OOP is crucial for simplicity and strictness of Litex.

"Forall Euclidean space S and x in S" in math can be translated to "forall [S Euclid_Space] x S: " in Litex. Here S is a type and Euclid_Space is the type of S, i.e. type of type.

```plaintext
// declare a concept

concept Group G: // suppose G is a group
    type_member:
        fn __mul__(g G, g2 G) G // define *
        var I G // define identity
    member:
        fn inv() G  // inverse a given group element
    cond:
        forall v1 G, v2 G, v3 G: // equivalent to G.__mul__ is associative 
            (v1 * v2) * v3 = v1 * (v2 * v3)
        forall v G:
            v * v.inv() = G.I
            v.inv() * v = G.I


// declare a function with type requirements

fn [G Group] multiply(g G, g2 G) G: // Type G must satisfy concept Group
    multiply(g, g2) = g * g2

// declare a proposition with type requirements

prop [G Group] element_wise_commutative(g G, g2 G) G:
    cond:
        g * g2 = g2 * g
```

In Litex, how do we describe the situation where certain sets can "implement" the concept (like group), meaning they can be endowed with a group structure? What does it mean when we say R1, R2 and R3 are Euclidean Space?

If you view a type as a set, then a concept is a "type of type" or a "set of sets". For example, the concept of a group can be thought of as the set of all sets that can be groups. Real is a type because there's only one set named Real, while there are multiple groups that implement the Group concept. R1, R2 and R3 are Euclidean Space actually means R1, R2 and R3 implements all features of Euclid Space. (Mathematically, it means certain sets being able to implement a category.)

Such ideas already exist in mainstream programming world for practical purposes. Types in Go (the Go programming language) implements interface. Implement means types have required members. Types in Litex implements concept. Implement also means types have required members.

In Go, interfaces can be directly passed as parameter types. In Litex, a concept should not used in that way. For instance, a function like "fn f[G Group, G2 Group](g1 G, g2 G2)" can't be written as "fn(g1 Group, g2 Group)". If written that way, there's no indication that "g1 and g2 might belong to different groups". That is why, in Litex, concept acts as a stricter interface and as a looser version of generics.

Type inference is possible. When calling f[G Group, G2 Group](g G, g2 G2), you can just write f(g, g2) instead of f[G, G2](g, g2) since G and G2 can be inferred.

Another question is, how do we describe the situation where one set "extends" another set (like complex number extend real number)?

In mathematics, to extend a structure (like the real numbers) means to create a larger structure (like the complex numbers) that includes the original structure as a subset while preserving its properties and adding new features (In category theory it is called embedding).

That is what "type implement another type" means in Litex. What does this extend mean? It means there is an injection from all variables from one type to another, members of original type implements the extended type and maintain its original features.

### Litex Statements

Congratulations, you have already learned most of important ideas about Litex. Feel free to try to write a some Litex code! You will be amazed at the fact that math is nothing but arrangement of symbols and propositions based on simple rules. That is what Litex is all about: just enough syntax to express math. Redundant features have no place in Litex.

There are some more Litex statements that I have not mentioned yet.

#### Existential Factual Expression

<!-- TODO -->

## Interesting Examples

_Simplify, simplify, simplify._

_--Steve Jobs_

The Litex syntax is extremely simple and well designed. It is flexible and universal enough to tackle any problem you might encounter, and is strict enough to avoid error in any form.

1. Formalize Mathematical Induction

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>axiom mathematical_induction(p prop):</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;cond:</code> <br>      
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$p(0)</code> <br> 
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;forall (n Nat) $p(n) {$p(n+1)}</code> <br> 
      <code>&nbsp;&nbsp;&nbsp;&nbsp;then:</code> <br> 
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;forall n Nat {$p(n)}</code> <br>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>theorem mathematical_induction {P : Nat → Prop} (base : P 0) (step : ∀ n, P n → P (n + 1)) : ∀ n, P n := by</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;intro n</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;induction n with</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;| zero => exact base</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;| succ k ih => exact step k ih</code> <br>
    </td>
  </tr>
</table>

As you can see in the example, it takes far less mental burden to formalize a theorem in Litex than in other languages. You don't need to remember and type in all those "base", "step", "intro", "induction", "exact", "succ" keywords. You don't need to remember unintuitive syntax. You don't need worry about anything unrelated to your main purpose. Just use a few Litex keywords then everything gets done. The only complexity comes from math itself, not from Litex.

## How to write good Litex code

_Beauty is the first test: there is no permanent place in the world for ugly mathematics._

_-- G.H. Hardy_

It is important to write clean and understandable proof. From my experience, there are several traps preventing you from writing good Litex code. You should key in mind not to fall into them:

- When translating a bad book written in natural language into Litex, you may encounter issues such as undeclared notation overloading, undefined symbols, new concepts appearing unexpectedly, and an abundance of vague statements like 'too simple to prove.' It's best not to translate such books directly into Litex. Instead, take the time to clarify your thoughts before writing them down.

- Don't generalize at the very beginning. Instead of generalizing your proposition or type members to Euclid Space of all dimensions, stick to special cases like R2 or R3 first. After that, use "impl" keyword to implement them into more generalized cases. Litex is flexible enough for you to start your proof from any level of abstraction.

In the near future, these poorly written books will fade away, as Litex offers a much clearer option for readers: how notations and theorems relate to one another can be visualized by Litex. No error would exist in any working Litex code.

## Conclusions

_The best way to predict the future is to invent it._

_-- Alan Kay_

Litex is simple to write, easy to read, It facilitates the construction of new concepts, the writing of intuitive proofs, and the seamless integration of different Litex codes. It is both enjoyable and efficient to write Litex.