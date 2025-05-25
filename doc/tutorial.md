# The Litex Formal Language Tutorial

**version 0.0.1-beta**

## Whetting Your Appetite

Everyone have started to think and reason since childhood. The ability to reason is what differentiates humans from animals. The reason why mathematical reasoning is strict, undeniable, and universal is that it follows a small set of rules so intuitive that it is kind of inherent in human nature. And miraculously, on top of those rules and another small set of axioms, we human beings are able to build the entire world of mathematics. All scientific, engineering, and economic theories are built upon mathematics.

If you are a software developer, or mathematician, or an AI researcher, you might have encountered formal languages. Formal languages are softwares where, people write down their reasoning without breaking the rules of the language, and the software will check if the reasoning are valid accordingly. It works like how a human checks whether a piece of math is correct, but in a more strict and automated way. Just like nobody can calculate faster than a calculator, nobody can check the validity of a piece of reasoning faster than a formal language. There is huge potential in using formal languages to check the validity of any piece of reasoning.

However, traditional formal verification languages like Lean4, Coq, and Isabelle are too complex and too far removed from everyday mathematical notation. These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. The fundamental reason for this complexity is that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system.

If Newton had to learn those theories before inventing calculus, he would never succeed, because those theories would be invented 3 centuries later.

Maybe you are a young teenager captivated by mathematics, eager to master the art of deductive reasoning and rigorous thinking, just like the ancient philosophers such as Plato or the brilliant detective Sherlock Holmes.

Maybe you are an AI researcher striving to develop reasoning models that can match or surpass human cognitive abilities. Formal mathematical data could enhance your model's reasoning capabilities and perhaps inspire the next breakthrough in model architecture.

Maybe you are a mathematics student seeking to streamline the paper review process, identify potential errors in your thesis, and collaborate with fellow mathematicians online - much like how programmers collaborate through platforms like GitHub.

Maybe you are a rocket scientist who needs absolute certainty in every mathematical formula, ensuring your spacecraft's precise trajectory to the moon.

Maybe you are simply an enthusiast who finds joy in appreciating the elegance of mathematics and discovering how individual concepts intertwine to create a magnificent tapestry of knowledge.

Litex is the perfect language for you.

## Using The Litex Interpreter, Tools, and Resources

<!-- Visit Official site [litexlang.org](https://litexlang.org), Github release [litexlang/golitex](https://github.com/litexlang/golitex) to download the Litex interpreter. -->

<!-- Online Playground: [litexlang.org](https://litexlang.org) -->

<!-- Both .lix and jupyter notebook are supported. -->

<!-- You can read tutorial, reference, blueprint on [litexlang.org](https://litexlang.org). -->

<!-- Follow us on Twitter, Discord, Github, and RedNote -->

## First Example

Let's try some simple Litex commands. Perhaps the most representative example of how reasoning works is Syllogism (三段论), proposed by Greek philosopher Aristotle.

```
set human
prop intelligent(x human)

know:
    forall x human:
        $intelligent(x)

obj Jordan human
$intelligent(Jordan) # check whether Jordan is self aware
```

What the above code means basically is:
- All humans are self aware.
- Jordan is a human.
- Therefore, Jordan is self aware. (This is the conclusion)

Let's explain the above code statement by statement.

```
set human
```

Modern mathematics is built upon set theory (Do not worry if you are not familiar with set theory. You will get familiar with it in the future). In Litex, we use `set` to define a set of objects. Here, we define a set of objects called `human`.

```
prop intelligent(x human)
```

`prop` is a Litex keyword referring to "proposition" in math. A proposition is a statement that is either true or false, and  mathematical proof of a proposition is a chain of logical deductions leading to the proposition from a base set of axioms.[^1]. Here we define a new proposition called `intelligent`, which is a proposition about an object `x` that is a member of the set `human`. 

Besides `true` and `false`, a proposition can also output `unknown` and `error` in Litex. If an there is no sufficient information to determine the truth value of a proposition, it will output `unknown`. For example, if we do not know whether Jordan is a human, the proposition `intelligent(Jordan)` will output `unknown`. If the user disobeys the rules of the language, it will output `error`.

In the following, we will use `factual statement` to refer to a statement that is either true or false, instead of `proposition`, to avoid confusion between proposition definition and proposition check.

In many Litex statements, you will find a parameter name followed by a set name. For example, `x human` means `x` is a parameter that can be replaced by any object in the set `human`. It works like how a type system works in programming languages like C or Go, but in a more flexible way. An object can be a member of multiple sets, which is not allowed in most programming languages.

```
know:
    forall x human:
        $intelligent(x)
```

Litex keyword `know` means the following statements are believed to be true by the user. For example, you can use `know` to define a new axiom, make a new assumption, or make a new conclusion. However, be careful when using `know`. If you make a wrong assumption, the whole reasoning process will be invalid. Factual statements in `know` statements will be stored in the `Litex knowledge base` of current context (in a more technical term, the current runtime environment).

The body of the `know` statement is indented. Indentation is Litex's way of grouping statements. You have to type a tab or spaces for each indented line.

Universal Quantification `forall` is a Litex keyword referring to "for all" in math. It means the following statement is true for all objects when parameters all satisfy given conditions. For example, `forall x human: $intelligent(x)` means the factual statement `intelligent(x)` is true for all objects `x` that are members of the set `human`. A factual statement is a statement that is either true or false, and must start with `$`.

```
obj Jordan human
```

Litex keyword `obj` introduces a new object into current context. When you use `obj` to introduce a new object, you have to specify the set that the object belongs to. For example, `obj Jordan human` means `Jordan` is a member of the set `human`.

```
$intelligent(Jordan)
```

`$intelligent(Jordan)` is a factual statement about the object `Jordan`. It tells the Litex interpreter to check whether `$intelligent(Jordan)` is true. The Litex interpreter will check it using known facts in the `Litex knowledge base` based on builtin rules. Do not worry about how the builtin rules works. You will be surprised at how easy they are. They are just the rules of logic that you have so frequently used in your daily life every single day. This tutorial will explain them later.

After running all the above code, the Litex interpreter will output the following result.

```
set human

prop intelligent(`x)

know:
    forall `x:
        then:
            $intelligent(`x)

obj Jordan

$intelligent(Jordan)
is true. proved by
forall `x:
    then:
        $intelligent(`x)

---
success! :)
```

When you see the smile face :), it means the proof is successful, Congratulations! If not, it means the proof is failed, there must be something `false` or `unknown` or `error` in your code. Read the error message carefully and fix it.

The first few lines of outputs are very similar to the input. Messages of `set`, `prop`, `know`, `obj` statements are just copy of the input. The only difference is that the output is there are some "\`" in the ouput. "\`" means that is a free variable, and the Litex interpreter will replace it with a concrete value when checking the factual statement. For example, x in `prop intelligent(x human)` is a free variable, and Jordan in `$intelligent(Jordan)` is a concrete value.

The most important part of the output is the last line. It means the `$intelligent(Jordan)` is true, proved by the previously known fact `forall x human: $intelligent(x)`.

Think about it, if it were you to check whether Jordan is intelligent, what will you do? You will look up the knowledge base, and find the fact `forall x human: $intelligent(x)` instead of `$intelligent(Jordan)` (It is illegal to write `forall` statements in a single line in Litex. In this tutorial, we write them within a line for better readability.). Then you will replace `x` with `Jordan` in the fact, and see whether `Jordan` satisfies all the conditions. In this case, the only condition is that `Jordan` is a human. Since we have already known that `Jordan` is a human by its deifnition, we can conclude that `$intelligent(Jordan)` is true. Litex does exactly the same thing for you, and it is much faster and more accurate than any human.

When a factual statement is proved, itself will be added to the `Litex knowledge base` for future use. For example, if you run the `$intelligent(Jordan)` statement again, the Litex interpreter will output the following result.

```
$intelligent(Jordan)
is true. proved by
$intelligent(Jordan)
Jordan = Jordan
```

Now it is verified by the new fact `$intelligent(Jordan)` itself instead of the previously known fact `forall x human: $intelligent(x)`. In math, you can either prove a fact by a universal quantification using `forall` statement, or prove a fact by itself. Previously, we proved the fact `$intelligent(Jordan)` by the a universal quantification. Now, we proved it by itself.

Congratulations! You have just learned the most basic usage of Litex through a simple example. See, it is not so difficult, right? That is the design choice of Litex. Litex is a tool that can help you to reason stictly and naturally at the same time. 

Learning Litex is different from traditional formal languages. You don't need to read thick books that make your brain explode. Instead, focus on connecting Litex with your intuition and common sense. The more you understand how Litex relates to your daily reasoning, the better you'll learn it.

There is two more things you should know: comments and `prove` statements. Many of the examples in this tutorial include the two to be clearer and more readable.

```
# This is a comment

"""
This is a multi-line comment
This is a multi-line comment
"""
```

Comments are used to explain the code. They are ignored by the Litex interpreter. You can use comments to help you understand the code better. There are two types of comments in Litex. The first one is the single-line comment, which is started with `#`. The second one is the multi-line comment, which is started with `"""` and ended with `"""`.

```
prove:  # prove opens a new proof context.
    obj Kobe human
    $intelligent(Kobe)

obj Kobe human # This Kobe is different from the Kobe in the prove context.
```

`prove` statements opens a new and local proof context. It can see all previous facts in the main context, but it cannot affect it. In this example, the `Kobe` object only exists in the `prove` context, and it is different from the `Kobe` object in the `obj` statement. After leaving the `prove` context, the `Kobe` object will be forgotten. `prove` is used to keep the main context clean and make small drafts.

OK! Let's move on to the detailed explanation of Litex. Let's start with the most basic and interestring statement: `forall` statement.

## `forall` statement

`forall` statement, also known as universal quantification, is the building block of the entire of math world. Without it, we cannot can not derive new facts from known facts. They are like using a single finite-length sentence to simultaneously describe countless facts.

For example, if we know that `forall x human: $intelligent(x)`, we can conclude that `$intelligent(Jordan)` is true. If Kobe is also a human, we can also conclude that `$intelligent(Kobe)` is true. No matter how many humans there are, we can always conclude that `$intelligent(x)` is true for any human `x`. This is very different from `$intelligent(Jordan)` or `$intelligent(Kobe)`, which are only true for Jordan and Kobe respectively. Facts like `$intelligent(Jordan)` are called `specific` facts.

There are several ways to write `forall` statements in Litex. Different ways have different purposes.

```
# Define some propositions
prop male(x human)
prop man(x human)
prop masculine(x human)

# No extra condition, no iff
forall x human:
    $intelligent(x)

# With extra condition, no iff
forall x human:
    $male(x)
    then:
        $man(x)

# With extra condition, with iff
forall x human:
    dom:    # dom means domain mathematically
        $male(x)
    then:
        $man(x)
    iff:
        $masculine(x)
```

## `exist` statement

`exist` statements, also known as existential quantification, is another collection of important factual facts in math in general. It works as the opposite of `forall` statements, since `not forall` means there exists at least one object that satisfies the condition of the `forall` statement but does not satisfy its conclusion.

Additionaly, `exist` statements are syntactically different from ordinary specific facts. 

## `not` statement

## `or` statement

`or` statements are used to combine multiple factual statements. If when a subset of the statements being false can lead to the validation of one of the other subset statements to be true, then the `or` statement is true.

```
prove:
    obj James human
    prop P(x human)
    or:
        $P(James)
        not $P(James)
```

This generic prop name `P` was intentionally chosen to emphasize universality. However, when writing Litex code, avoid such naming conventions - always use descriptive names that convey meaning for better readability.

The `not` statement is used to negate a factual statement. Since a factual statement is either true or false, the `or` statement must be true.

## Factual Statements

Now you have learned the most basic and important statements in Litex: `forall`, `exist`, `or`, `specific` facts. I hope learning them did not make you lose too much brain cells. They have exactly the same meaning as what you have been using in your daily life. What you just learned is just how to express them in a more formal way in Litex.

You might be wondering, what other factual expressions do I need to know? Are there infinitely many of them? The answer is NO. NO. There are exactly just four of them. YOU CAN BUILD THE ENTIRE WORLD OF MATH WITH JUST FOUR OF THEM. These four keywords are basis of first-order logic statements, and 99.99% of math that you are familiar with are built upon them.

**warning: There is a mathematical field called higher-order logic and might be covered in future versions of Litex. It allows you to quantify over propositions, and even over sets. However, most of the math that you are familiar with are built upon first-order logic, with just one exception: the mathematical induction. Don't worry, it is a speical keyword of Litex. If you do not know what high-order logic is, don't worry. It is not the mainstream of math and does not affect your understanding of Litex.**

## Proof Related Statements

Previously, we have learned `prove` statement. They are used to open a new and local proof context. In this context, you can prove new facts without affecting the main context.

There are several more statements related to proof. `prove_by_contradiction` is used to prove a statement by contradiction. `prove_in_each_case` is used to prove a statement by cases. `prove_or` is used to prove a `or` statement. `prove_by_or` is used to prove a specific fact using `or` statement.

```
prove:
    prop P(x N)
    prop Q(x N)
    obj n N
    
    know:
        forall x N:
            $Q(x)
            then:
                not $P(x)
        
        $P(n)

    prove_by_contradiction:
        not $Q(n)
        prove:
            $Q(n)
            not $P(n)
```

`N` is a keyword in Litex, meaning the set of natural numbers. `P` is a proposition about a natural number `x`.

In natural language, the above example says all natural numbers `x` are such that if `Q(x)` is true, then `P(x)` is false. And we know that `P(n)` is true for some natural number `n`. Therefore, `Q(n)` must be false, and we prove it by contradiction: assume `$Q(n)` is true, then `$Q(n)` is true, then `not $P(n)` is true. The interpreter checks whether the opposite of the last statement of `prove_by_contradiction`, which is `$P(n)` is true. And in this case, it is true because it is known. Now `$P(n)` and `not $P(n)` are both true, which is a contradiction. Therefore, the assumption `Q(n)` must be false.

```
prove:
    obj Joker human
    prop P(x human)
    prop Q(x human)
    prop R(x human)

    know:
        or:
            $P(Joker)
            $Q(Joker)

        forall x human:
            $P(x)
            then:
                $R(x)

        forall x human:
            $Q(x)
            then:
                $R(x)

    prove_in_each_case:
        or:
            $P(Joker)
            $Q(Joker)
        then:
            $R(Joker)
        prove:
            $R(Joker)
        prove:
            $R(Joker)
```

`prove_in_each_case` works like this: first, we check the `or` statement. If the `or` statement is true, then we check the `then` statement at each case. For example, first we assume `$P(Joker)` is true, then we check the `then` statement in the first `prove` statement, which is `$R(Jokter)` here. This example is easy, and we get `$R(Joker)` immediately because `forall x human: $P(x) then $R(x)` is known. Then we check the second case, which is `$Q(Joker)` is true and see whether `$R(Joker)` is true. Since we know that `forall x human: $Q(x) then $R(x)`, we can conclude that `$R(Joker)` is true. Therefore, the `prove_in_each_case` statement as a whole is true.





## `suppose` and `with` Statements

## Special keywords

## Modules

## Words From The Inventor

Hi, I am Jiachen Shen, the creator of Litex. I am a PhD student in mathematics, and but I am also a programming language geek. I have been working on Litex since 2024 and received many valuable feedbacks from Litex enthusiasts. I hope you enjoy using Litex, too. Feel free to contact me if you have any questions or suggestions via [github](https://github.com/litexlang/golitex) and [mail](litexlang@outlook.com). Obviously, Litex is far from perfect. It is still in the early stage of development. Any feedbacks are welcome.

[^1]: [Mathematics for Computer Science](https://courses.csail.mit.edu/6.042/spring18/mcs.pdf)

