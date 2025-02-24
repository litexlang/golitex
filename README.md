# Litex: A Minimalist Proof Assistant

<div align="center">
<img src="assets/logo.png" alt="The LiTeX Logo" width="300">

</div>


## About

_That language is an instrument of Human reason, and not merely a medium for the expression of thought._

_–- George Boole_

Litex is a minimalist proof assistant (formal language). Since even children grasp math naturally, a formal language design should exist that's easily understood and used by anyone. The goal of Litex is to invent such a language. The implementation approach leverages a profound understanding of the commonalities and distinctions between programming and mathematics.

Traditional proof assistants lack the fluidity and ease needed to scale formal proofs, while Litex handles the growing complexity of modern mathematics effectively through its well-designed syntax. Litex is designed to be as  intuitive as Python or LaTeX, with a minimal learning curve. Users can trust their common sense to write Litex.

Litex has the potential to greatly impact both mathematics and AI:

- **For Mathematics**: 
  - **For individual researchers**, it provides peace of mind by reducing the risk of subtle errors undermining their proofs.
  - **For the whole mathematics community**, since Litex ensures correctness, the need for paper reviews is eliminated. This fosters trust and enables large-scale collaboration, akin to a "GitHub for Math," while also supporting interactive math textbooks.

- **For AI**:
  - **More Formal Data**:
Because Litex is an order of magnitude simpler than traditional proof assistants, LLMs may require far fewer datasets to develop the ability to translate existing mathematics into Litex, accelerating formal data growth. The potential large user community also helps provide high-quality data.

  - **Automated Verification**:
Litex can automatically verify LLM outputs for math problems, providing a reliable way to validate and refine their reasoning. This capability is crucial for improving the accuracy and robustness of LLMs in mathematical tasks.

In short, Litex can transform workflow and collaboration of mathematicians. It boost AI's reasoning with more formal data and a super efficient verifier. More people will adopt Litex because of its simplicity and powerful capabilities.

## Getting Started

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

Let us begin with a quick introduction to Litex. Our aim is to show the essential elements of the language, but without getting bogged down in details, rules, and exceptions.

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

<!-- TODO: I have not implemented the type of function and prop yet. -->

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
fn add(a Real, b Real) Real

// declare a proposition

prop younger(a Human, b Human):
    cond:
        a.age < b.age
```
<!-- TODO: Better -->
In Litex, `type` has the following functionalities:

- **Set Membership**:
The statement var x type_name means that x has the type type_name. Mathematically, this means x belongs to the set called type_name. For example, `var n Real` means n is a real number, i.e., n is in the set of all real numbers. As in most programming languages, every object has a type. However, the object might not have a specific "value" because, in many cases, it is the type of the variable (not its value) that determines its relationships with other objects. For example, no matter what a positive number equals to, it is larger than 0. Since a variable can belong to multiple sets (e.g. 1 is both a real number and a natural number), a variable can have multiple types.

- **Determine Meaning of Operations**:
Objects of different types support different operations and propositions. For example, when a and b are positive natural numbers, expressions like a^b (multiplying a by itself b times) and a < b are well-defined and meaningful. However, when a and b are matrices, operations like a^b and a < b are not standard notations and may not make sense. Importantly, an object should never be passed to a proposition or function if the parameter types do not match the type of that object. This ensures that operations and functions are applied only in contexts where they are well-defined.

- **Own Members**:
In programming, a type is typically called a "struct" (in C) or a "class" (in C++ or Python). Objects of different types can have different members. For example, a human Bob might have an attribute Bob.age. Additionally, the type itself can have members. For example, `S Rn` means S is an Euclidean space and S.dim could represent the dimension of the space.



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

