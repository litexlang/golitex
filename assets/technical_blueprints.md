## What makes Litex Special

### Litex Approach: A Fancy Dictionary (Database) of Mathematical Facts

Mathematics involves two different major tasks: computation and verification. Computation (e.g. arithmetic computation, symbolic computation), handled by programming languages, alters memory states and requires control flow (e.g. loops, conditionals) and literal transformations to manage operations.

Verification is akin to searching a dictionary: you use a key to find relevant information. In mathematical verification, you take an expression and search a dictionary of known facts for supporting evidence. While it involves more rules than a simple lookup, the core idea remains the same. Unlike computation, verification doesn’t alter memory states. Litex’s implementation is based on these principles.

When you find evidence for an expression, it becomes `true` and is added to the dictionary of known facts. Math works this way: you create new "keys," search for facts to verify them, and if successful, the key joins the dictionary. What is why Litex is implemented as a fancy "dictionary" ("database") of known facts allowing users to search (verify) and insert (store new facts) easily.

### Difference between Litex and Traditional Proof Assistants

One of the most innovative mind of out time, Steve Jobs, said: If you define the problem correctly, you almost have the solution. The whole Litex project is an exploration of what does “minimalist formal proof assistant” actually mean.

Existing formal languages are notoriously hard to read and write, even for the most talented mathematicians. This is because they are built as general-purpose languages, requiring them to include syntax unrelated to mathematical proofs such as memory state alterations (control flows, arithmetics), which adds unnecessary complexity. At the end of the day, they are just general-purpose languages that are more adept at mathematical verification compared to other mainstream languages like Python.

On the other hand, Litex is focused on verification and does not support general-purpose computation, as a design decision. Its syntax is entirely grounded in everyday mathematical expressions, without compromising its clarity for unrelated functionalities. 

At a deeper level, it is the inherent simplicity of mathematical reasoning or verification itself that makes Litex simple. Litex takes huge effort to figure out what logical rules are governing mathematical reasoning. It amazingly turned out that there aren’t many of them. From hindsight, such small number is predictable: even a 5-year-old child have a natural grasp of how reasoning works, and he/she does not need even to be taught how to do that!

That is how Litex brings simplicity to the extreme: it just four outputs: `true`, `false`, `unknown`, and `error`; it just has no more than 20 keywords; it just has 3 factual expressions: specific, conditional and universal. Having one extra feature is redundant, while missing one might make users uncomfortable or prevent certain logics from being implemented. General-purpose functionalities are implemented as plugins instead of builtin syntax to avoid distracting from the core task of verification.

Within other proof assistants, there is a much smaller and cleaner language akin to Litex struggling to get out. Litex presents users with exactly what they need, no more and no less, sparing them the mental gymnastics of configuring it themselves.

In short, **The fundamental difference** between Litex and traditional proof assistants (e.g. Lean4, Coq) is this: Litex applies programming techniques to mathematics, while others apply mathematical techniques to programming. This is why tools like Lean4 require users to learn advanced math, such as type theory, whereas Litex only requires basic programming skills — no harder than Python or LaTeX — and their innate ability to reason.

## Litex Expressions

There are only two kinds of expressions in Litex: constructive expressions and factual expressions. Factual expressions are used by the user to declare some facts as true. Litex then verifies whether these facts are indeed correct. If they are correct, these new facts are added to the proof environment, where they can be used to verify subsequent facts. Constructive expressions are for introducing new elements in proofs, such as new types, new objects, new functions, or new structs.

### Factual Expressions

#### Outputs of Factual Expressions

Every Factual expression of Litex has just four kinds of outcomes: true, false, unknown, error. 

- **True**: Litex confirms your expression based on known facts.

- **False**: Litex disproves your expression based on known facts.

- **Unknown**: Litex cannot find relevant facts to conclude.

- **Error**: Your input is incorrect, e.g., a typing mistake.

This mirrors how Humans think when reading proofs: confirming correctness (true), spotting falseness (false), being unsure (unknown), or encountering input issues like syntax error (error).

Previous formal languages(proof assistants), such as Lean4 and Coq, are still general-purpose languages. They support execution, arithmetic, and control flow, which prevents their syntax from focusing solely on theorem proving and requires them to accommodate other functionalities. This results in highly redundant syntax.

Litex, free from execution constraints, functions like a regex matcher or SQL query processor, validating structured statements against formal rules. Adding unnecessary features would dilute its expressive power, that is why Litex expressions only have four outcomes. Execution in Litex is possible but delegated to plugins, not the language itself.

#### Specific, Conditional, Universal Factual Expressions

There are different kinds of factual expressions: specific (instantiated), conditional (begin with keyword `if`) and universal expressions (begin with keyword `forall`):

```plaintext
// Comments are written after "//".
obj Bob Human

// specific
Bob is self_aware

// conditional
if:
    Bob.age = 10    // conditions
    then:
        Bob is young    // results

// universal
forall x Human, y Human:    // declare objects in the universal expression
    cond:
        x.age < y.age   // conditions
    then:
        younger(x,y)   // results
```

Different factual expressions have distinct meanings and are processed differently by the Litex interpreter. This means they are verified differently and, when stored in the proof environment, are used in unique ways to prove newly input facts.

```
if:
    Bob.age = 10    // conditions
    then:
        Bob is young    // results
```

When the user input a conditional expression, the interpreter first opens a new proof environment, the interpreter set all conditions to be true and verifies resulting factual expressions. If all results are true, the conditional expression is true.

```
forall x Human, y Human:    // declare objects in the universal expression
    cond:
        x.age < y.age   // conditions
    then:
        younger(x,y)   // results

forall x Human:
    x is self_aware // If there is no further condition, 'cond' and 'then' can be eliminated
```

When the user input a universal expression, the interpreter first opens a new proof environment and declare objects written after the 'forall' keyword in this new environment. In this new environment, the interpreter set all conditions to be true and verifies resulting factual expressions. If all results are true, the universal expression is true. Notice the main difference between the conditional expression and the universal expression is whether new objects are involved.

```
// Different forms of specific factual expressions

Bob is self_aware

self_aware(Bob)    // equivalent to Bob is self_aware

1 < 2

less_than(1,2) // If a proposition receives more than one argument, you should use  as prefix for proposition name.

Real.__lt__(1,2) // equivalent to 1 < 2. Notice a type can have propositions as member.
```

When the user inputs a specific expression, the interpreter searches the current proof environment for known facts with the same proposition name. These facts may be specific, conditional, or universal. If the given specific fact exactly matches a known specific fact or satisfies a conditional or universal expression, it is considered true. Otherwise, the specific expression remains unknown.

There are several different ways to call a specific factual expression:

- If there is only one parameter, you can write parameterName is propositionName

- If there rae more than one parameter, you write propositionalName(parameters). ""  has no extra meanings. It is just a symbols used by a user to distinguish between functions and propositions.


#### Existential Factual Expressions

There is one important kind of specific factual expression: existential factual expressions:

```
// declare a existential proposition

exist_prop exist_nat_less_than(n Nat):
    have: // when being called by have statement, objects below will be introduced in proof environment
        obj m Nat
    then:
        m < n

know forall n Nat:
    cond:
        n > 0
    then:
        exist_nat_less_than(n)

exist_nat_less_than(100) // As a specific factual expression, it is true.

have m Nat: exist_nat_lss_than(2)   // Introduce new object, m, to current proof environment
```

Notice when being verified as a specific factual expression, there is no difference between existential factual expressions and ordinary specific expressions. The only difference between existential factual expressions and ordinary specific expressions is, it can be called in "have statement", which is a safe way to introduce new objects in current environment.


### Constructive Expressions

Every fact must be associated with some concrete object or entity; it cannot exist independently without being tied to something specific. There are three kinds of entities in Litex: object(obj), function(fn), and proposition(prop). The user must first declare a object before using it. Any entity has a type.

<!-- TODO: I have not implemented the type of function and prop yet. The major obstacle is: if I view cond as a component of a prop or fn, how to implement this? Or should I just pass undefined f like fun(f fun) and wait till the runtime to check validation of type? I guess f fn wait of doing is every reasonable    existential propositions are used in the same way as how ordinary propositions. The only difference between existential propositions. exist is eql to not forall-->

```plaintext
// declare a type

type Human:
    member:
        obj age Natural
```
<!-- TODO: Better -->
In Litex, `type` = `set` + `structure`. The set defines the possible values of the data, while the structure (such as operations, special elements, or axioms) gives the data specific behaviors or constraints. The way to define a structure is by specifying different `type_member` and `member`.

For example, the set of integers can be equipped with a structure that includes the operations of addition (+), subtraction (−), and multiplication (×). This combination of a set (ℤ) and its operations (+, −, ×) along with special elements (like 0) defines the structure of the set of integers.

The same set can have different structures on it. For example, C[0,1] (the set of continuous functions on the interval [0,1]), different norms (such as the L1 norm or the L^∞ norm) impose different structures on the same set. Even though the underlying set is the same, the additional structure (the norm) defines different properties (such as convergence or completeness), making them distinct mathematical objects. 

The analogy between "program = data structure + algorithm" and "type = set + structure" highlights a fundamental similarity: both structs combine static properties (data structure or set) with dynamic behaviors (algorithm or structure) to define a complete entity. In programming, this forms the basis of functionality, while in math, it defines the characteristics and constraints of objects.

So, When the underlying set is different, the type must be different. Even if the sets are the same, if the structures imposed on them are different, they are considered distinct types.

In traditional mathematical notation, it is common to embed all relevant information directly into symbols. This practice is somewhat analogous to programming, where symbols like `1`, `2`, or `3` literally encode their own values. However, sometimes this approach can lead to confusion, particularly in formal contexts. For example, the notation \( \math{R}^n \) represents an \( n \)-dimensional space, where \( n \) can be any number. This introduces ambiguity because \( n \) is merely a placeholder for the dimension, and many properties of Euclidean spaces do not depend on the specific value of \( n \). 

In programming, such information is typically encapsulated within an instance of a type, separating the object itself from its properties. Adopting a similar approach in mathematical notation could improve clarity and rigor by distinguishing between the structure (e.g., the space) and its metadata (e.g., its dimension). This would make it easier to reason about mathematical objects in a more abstract and formal way, making Litex code more modular and sharable across different users.

<!-- TODO: "A impl B" is where abstraction layer changes: B is higher abstraction, A is lower. If you want to jump between abstraction layer, use impl. Here A can be struct or type, B is struct. NEED TO EMPHASIZE THAT JUMPING BETWEEN DIFFERENT ABSTRACTION LAYER IS DONE BY impl -->


`type` has the following functionalities:

- **As as Set**:
The statement obj x type_name means that x has the type type_name. Mathematically, this means x belongs to the set called type_name. For example, `obj n R` means n is a R number, i.e., n is in the set of all R numbers. As in most programming languages, every object has a type. However, the object might not have a specific "value" because, in many cases, it is the type of the object (not its value) that determines its relationships with other objects. For example, no matter what a positive number equals to, it is larger than 0. Since a object can belong to multiple sets (e.g. 1 is both a R number and a natural number), a object can have multiple types.

- **Determine Meaning of Operations**:
Objects of different types support different operations and propositions. For example, when a and b are positive natural numbers, expressions like a^b (multiplying a by itself b times) and a < b are well-defined and meaningful. However, when a and b are matrices, operations like a^b and a < b are not standard notations and may not make sense. Importantly, an object should never be passed to a proposition or function if the parameter types do not match the type of that object. This ensures that operations and functions are applied only in contexts where they are well-defined.

- **Own Members**:
In programming, a type is typically called a "interface" (in C) or a "class" (in C++ or Python). Such technique of organizing code is called "object oriented programming (OOP)". Objects of different types have different members. For example, a human Bob might have an attribute Bob.age. Additionally, the type itself can have members, which works like "static member" in C++. (A Member can be viewed as "there exist an unique object with certain properties". So "member" is a syntax sugar of "uniquely exist". Uniqueness is essential because strictness of math comes from uniqueness, i.e. no other choices.)

- **implement a struct or extend existing types**:

<!-- function that returns new functions or new propositions are not implemented -->

<!-- TODO: below are not well written -->

Everything in Litex is represented by a symbol(a single word). Objiables, Functions, Types, propositions are all represented by a single symbol or composited symbol. Function, object and proposition are called first-class citizens of Litex, because they can be passed to function/proposition parameters and behave as return value.

``` text
// declare a object

obj Bob Human: // object name is Bob, object type is Human
    Bob.age = 10 // Age of Bob is known to be 10

obj Alice Human // just declare a object, no extra known factual expressions involved

have m Nat: exist_nat_lss_than(2)
``` 

In mathematics, a object is a symbol (often a letter like x,y,z) that represents something that have some factual expressions. Objiables are used in factual expressions.

Notice the object you introduce to current environment might not exist. For example, the type of your object might be an empty set. To make object declaration safe, you can use "have" statement. "have" statement is valid only when the related existential factual expression is true.

<!-- HERE WE LACK HOW TO INTRODUCE A GROUP OF VARIABLES LIKE NAT USING REGEX -->

```plaintext
// declare a function

// input 2 objects with type R, output object with type R
fn add(a R, b R) R:
    then:
        add(a, b) = add(b, a)   // facts about function add

// use "return" value as parameters of a factual expression: equal expression.
add(1 ,2) = add(2, 1)
1 + 2 = 2 + 1
```

Functions in Litex are not executed. In the Rm of mathematics, a function is essentially an entity that is eligible to precede a set of parentheses (). It shares similarities with what we refer to as a object, with the distinctive feature being its ability to be positioned before the ().

Function parameter list can receive first-class citizens. Function type list can receive type struct pair. You can bind conditions to parameters that appear in function parameters list. The result of the function output have some properties, which appear in then block.

In Litex, `obj` could essentially be entirely replaced by `fn`, `fn` object is simply a more versatile version of `obj` object: `fn` has the capability to precede parentheses (). For the time being, Litex retains `obj`, but its future necessity remains uncertain.

``` text
// declare a proposition

prop younger(a Human, b Human):
    cond:
        a.age < b.age
```

All specific factual expressions have related proposition name. For example, a = b have related proposition =, a < b have proposition <, red(a) have proposition red, subsetOf(x,y) have related proposition subsetOf. Actually you can view Litex proposition as Functions in mainstream programming languages because the "execution" of a "called proposition" (factual expression) outputs outputs: true, false, error, unknown.

The difference between a proposition (prop) and a factual expression is that a prop simply assigns a name to a statement, without determining its validity. On the other hand, a factual expression is meant to be evaluated, yielding an output value of true, false, unknown, or error.

<!-- There is no struct parameter list because you can infinitely iterate over that and If you truly what to bind properties to a struct, you should invent math in Litex and make what you are thinking about in object and add layer to that object. -->

<!-- You can make everything a function, because function are just objects that can appear before the () in expressions like f(). If you bind no extra features to that function, e.g. fn f() any. then f works like a object. -->

<!-- challenge: how to implement or as syntax sugar?  -->

```plaintext
struct Euclid_Space S:   // suppose S is a Rn
    type_member:
        obj dim Nat // dim is positive natural number
        fn __add__(v1 S, v2 S) R
    member:
        fn __at__(n Nat) R: // define @, which means the nth index of the 
            cond:
                n < S.dim
    cond:
        forall v1 S, v2 S:  // define addition of two vectors
            forall k Nat:
                (v1 + v2)@k = v1@k + v2@k
```

In this example, we define a struct called Euclidean Space. Sometimes it is crucial to pass "the type of the type" to a proposition, just like how programmers uses templates to pass parameter types to functions. That is where struct comes into place.

Euclidean space is a set of all finite dimensional spaces. S.dim represents the dimension of the space. Typically we write "Let S is R^{n}, where n can be any natural number", now we just write "S Euclid" and S.dim is automatically reserved for us. Notice how undefined objects "x" or "n" are "hidden" as a member of another symbol here. That is why OOP is crucial for simplicity and strictness of Litex.

"Forall Euclidean space S and x in S" in math can be translated to "forall [S Euclid_Space] x S: " in Litex. Here S is a type and Euclid_Space is the type of S, i.e. type of type.

<!-- TODO: Explain why operator is important here. 
Explain every time you define a type, a special member is automatically generated for you _ -->

```plaintext
// declare a struct

struct Group G: // suppose G is a group
    type_member:
        fn __mul__(g G, g2 G) G // define *
        obj I G // define identity
    member:
        fn inv() G  // inverse a given group element
    cond:
        forall v1 G, v2 G, v3 G: // equivalent to G.__mul__ is associative 
            (v1 * v2) * v3 = v1 * (v2 * v3)
        forall v G:
            v * v.inv() = G.I
            v.inv() * v = G.I


// declare a function with type requirements

fn [G Group] multiply(g G, g2 G) G: // Type G must satisfy struct Group
    multiply(g, g2) = g * g2

// declare a proposition with type requirements

prop [G Group] element_wise_commutative(g G, g2 G) G:
    cond:
        g * g2 = g2 * g
```

In Litex, how do we describe the situation where certain sets can "implement" the struct (like group), meaning they can be endowed with a group structure? What does it mean when we say R1, R2 and R3 are Euclidean Space?

If you view a type as a set, then a struct is a "type of type" or a "set of sets". For example, the struct of a group can be thought of as the set of all sets that can be groups. R is a type because there's only one set named R, while there are multiple groups that implement the Group struct. R1, R2 and R3 are Euclidean Space actually means R1, R2 and R3 implements all features of Euclid Space. (Mathematically, it means certain sets being able to implement a category.)

Such ideas already exist in mainstream programming world for practical purposes. Types in Go (the Go programming language) implements interface. Implement means types have required members. Types in Litex implements struct. Implement also means types have required members.

In Go, interfaces can be directly passed as parameter types. In Litex, a struct should not used in that way. For instance, a function like "fn f[G Group, G2 Group](g1 G, g2 G2)" can't be written as "fn(g1 Group, g2 Group)". If written that way, there's no indication that "g1 and g2 might belong to different groups". That is why, in Litex, struct acts as a stricter interface and as a looser version of generics.

Type inference is possible. When calling f[G Group, G2 Group](g G, g2 G2), you can just write f(g, g2) instead of f[G, G2](g, g2) since G and G2 can be inferred.

Another question is, how do we describe the situation where one set "extends" another set (like complex number extend R number)?

In mathematics, to extend a structure (like the R numbers) means to create a larger structure (like the complex numbers) that includes the original structure as a subset while preserving its properties and adding new features (In category theory it is called embedding).

That is what "type implement another type" means in Litex. What does this extend mean? It means there is an injection from all objects from one type to another, members of original type implements the extended type and maintain its original features.

### Litex Statements

Congratulations, you have already learned most of important ideas about Litex. Feel free to try to write a some Litex code! You will be amazed at the fact that math is nothing but arrangement of symbols and propositions based on simple rules. That is what Litex is all about: just enough syntax to express math. Redundant features have no place in Litex.

There are some more Litex statements that I have not mentioned yet.

<!-- TODO -->

## Interesting Examples

_Theory and practice sometimes clash. And when that happens, theory loses. Every single time._

_--Linus Torvalds_

The Litex syntax is extremely simple and well designed. It is universal enough to tackle any problem you might encounter, and is strict enough to avoid errors.

Nobody can learn programming just by reading manuals. Practice is the sole criterion for testing truth. So, follow the examples, write some code, get your hands dirty, and experience the miracle of Litex!

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
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;p(0)</code> <br> 
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;forall (n Nat) p(n) {p(n+1)}</code> <br> 
      <code>&nbsp;&nbsp;&nbsp;&nbsp;then:</code> <br> 
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;forall n Nat {p(n)}</code> <br>
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

- When translating a bad book written in natural language into Litex, you may encounter issues such as undeclared notation overloading, undefined symbols, new structs appearing unexpectedly, and an abundance of vague statements like 'too simple to prove.' It's best not to translate such books directly into Litex. Instead, take the time to clarify your thoughts before writing them down.

- Don't generalize at the very beginning. Instead of generalizing your proposition or type members to Euclid Space of all dimensions, stick to special cases like R2 or R3 first. After that, use "impl" keyword to implement them into more generalized cases. Litex is flexible enough for you to start your proof from any level of abstraction.

- Global objects are dangerous. Only the most important objects, like empty_set, should be used globally. Temporary objects like 'x' or 'n' must be enclosed in a local scope.

- Detailed Naming is recommended. When you formalize a new struct, a new function, or a new object, please write the meaning or purpose of that symbol in its name. Otherwise, people soon forgets what function "f()" means.

- If the same pattern of proof appear again and again, you should enclose such kind of proof in a single `forall` expression or a proposition.

As you can see, the good practice of writing Litex closely aligns with the good practice of writing any programming language. Clean code is always more maintainable, more extensible and more understandable. Following a good practice is the premise of clean code.

In the near future, these poorly written books will fade away, as Litex offers a much clearer option for readers: how notations and theorems relate to one another can be visualized by Litex. No error would exist in any working Litex code.

Finally, do not forget to improve yourself through practice, that is, by writing lots of code and read lots of code.

## Conclusions

_Simplify, simplify, simplify._

_-- Steve Jobs_

Litex is simple to write, easy to read, It facilitates the construction of new structs, the writing of intuitive proofs, and the seamless integration of different Litex codes. It is both enjoyable and efficient to write Litex.

Good writing simplifies math, while poor writing complicates it. Leibniz's calculus notation \frac{dy}{dx} surpassed Newton's \dot{y} for its clarity, just as Arabic numerals (1, 2, 3) outperformed Roman numerals (I, II, III) in simplicity.  Litex’s intuitive, everyday math-based syntax makes formal verification accessible and fluid, advancing reasoning and proof scalability.

## How is Litex designed as it is.

_Perfection is achieved, not when there is nothing more to add, but when there is nothing left to take away. _

_--Antoine de Saint-Exupéry_

The followings are design choices of Litex and how they are made. As Bjarne Stroustrup(inventor of C++) said: "Language design is a curious mixture of grand ideas and fiddly details". If you want to have a deeper understanding of Litex, the following will serve as a very good mental entertainment.

Why could Litex be so simple 

Fundamental reason: The simple reason is that the rules that governs human reasoning are not that many. Only three factual expressions are possible. Only 4 outputs of factual expressions.

### What makes Litex Factual Expressions easier to use

In Lean 4, every fact must have a name, and users must explicitly reference these names to use them in proofs. This forces users to remember even the most trivial facts, often with long and complex names, creating unnecessary burden.

Litex, on the other hand, automatically searches all known related facts (facts that have the same proposition name) to verify the current input, eliminating the need to manually recall and reference fact names. While users can still name facts if desired, it is no longer mandatory. This approach significantly improves the writing experience and makes Litex code cleaner and more intuitive compared to traditional proof assistants.

You can understand the aforementioned functionality in this way. Low-level programming languages, such as C, require users to manually manage memory. In contrast, modern languages like Python feature garbage collection, eliminating the need for users to name every newly allocated memory block or handle them with excessive caution. In our case, traditional proof assistants require users to manually "call" known facts to prove new facts. Litex eliminates that need. 

When the inverse of input factual expression is true, the interpreter outputs false. When the input does not obey syntax rule of Litex, the interpreter outputs error.

### Values of Factual Expressions are not "Values" of Functions

In Python, it is legal to write f(1 < 2), here the function f receives the result of 1 < 2 as input.

In Litex, passing a factual expression like "1 < 2" to a function is illegal because its output is emitted outside the Litex runtime. Only objects, functions, and propositions can be passed. To use boolean values, you must first formalize boolean theory within Litex. Avoid conflating internal function "values" with "external world" values.

Any mechanical algorithm can be formalized by math. Ideally, since Litex is mechanical, and since Litex is designed to formalize math, the users should be able to formalize Litex in Litex.

### When are mechanical algorithms necessary?

The Litex runtime does not include control flow (loops and branches) because people do not them when verifying codes. After all, nobody iterates over the same procedure in his/her brain for thousands of times to when they read a new line of proof. Instead, they use `forall` statements to "represent" the whole iteration process.

However, Litex still enables you to do mechanical things through language plugin. You can call a mechanical algorithm to help you generate text. This text can be implicitly embedded to your current line of your proof. In this way, Litex becomes "Turing complete" while vanilla Litex is not.


### C-flavored Type Naming Instead of Generics.

There is no generics in Litex, at least for the time being. I prefer single-word type name as how C works, rather than type with layers of layers of "<>"s, as how code looks like in C++ and other languages with generics(templates). 

Generics helps you to expose every layer of data-structure. It is great in many cases, but may cause serious trouble in Litex. The reason is simple: there are just so many layers of abstraction in math, too many to imagine. Exposing all the abstraction layers in type would make the code overly redundant. Users do not need to delve into structs that are too low-level.

### Users can start his proof from any abstraction layer.

In modern math, many facts are derived from set theory, a highly abstract foundation. However, math historically evolved differently. Natural numbers emerged in prehistory, and calculus was developed by Newton and Leibniz without set theory. A formal language that forces users to start from a fixed abstraction layer is limiting.

Mathematical discovery occurs in two ways: inventing abstract structs and finding concrete examples, or identifying patterns in facts and summarizing them into abstract structs. Both top-down and bottom-up approaches coexist in math, which is why Litex is designed to handle all levels of abstraction effectively.

### Formalize Litex in Litex

One of the most interesting struct in Computer Science is recursion. Since any mathematical process, including the Litex interpreter, can be formalized by math, and math can be formalized by Litex, I am looking forward to formalizing the pipeline Litex in Litex.

Don Knuth's marvelous book the art of computer programming taught us the mathematical definition of computer programming. For fun, take a look at it:

A mathematical definition of an **algorithm** in terms of set theory defines a **computational method** as a quadruple \((Q, I, \Omega, f)\), where:

- \( Q \) is a set containing subsets \( I \) (the set of inputs) and \( \Omega \) (the set of outputs).
- \( f \) is a function from \( Q \) to itself.
- \( f \) leaves \( \Omega \) **point-wise fixed**, meaning \( f(q) = q \) for all \( q \in \Omega \).

A **computational sequence** is then defined recursively as:
\[
x_0 = x, \quad x_{k+1} = f(x_k) \quad \text{for } k \geq 0.
\]
A computational sequence **terminates in \( k \) steps** if \( x_k \) is in \( \Omega \) for the smallest such \( k \). The **output** of the computation is \( x_k \). 

Finally, an **algorithm** is a computational method that **terminates in finitely many steps for all inputs in \( I \)**.

## Answers for typical questions

Litex searches its fact base each time it needs to verify a new fact. Does this method scale without losing speed?  

Yes. Even with a base of 10 million stored facts, it takes only about 10 seconds to verify those facts against the stored data. If this still seems slow, Litex's modular design allows you to manually exclude irrelevant facts to optimize performance.

Why does Litex has a chance of succeeding?

In computer science history, Overly complex and sophisticated software is often threatened by unknown, seemingly "simple" newcomers that rise unexpectedly. For instance, CISC is now significantly challenged by RISC—a shift that seemed improbable just a decade ago. Litex is a similar case.

However, Severe restriction on time and no budget forces me to go back to common sense, polish my ideas again and again until Litex is as simple as possible. That is where the clean syntax comes from: belief in minimalism, high focus, full passion.

Litex is based on what theory?

There are only two types of programming languages: to prove an idea, or to get things done. Litex is definitely of the second type. Litex is, and will remain to be, very pragmatic. Curious people might ask me "what theory is Litex based on". My answer is "Litex is invented by common sense, not by theory". The only "theory" of Litex is that there is no theory.

Does some math exist that Litex can not express?

Litex is supposed to be able to express ANY math. People might doubt that it is impossible to express all math with so few keywords. My answer is, with so few keywords, Python is Turing complete and in theory able to express programming.

When time is suitable, I will prove any Lean4 or Coq code can be written in Litex and through that way to prove logical completeness of Litex. The doubt is reasonable and it's exciting to conquer that problem.