# The Litex Formal Language Tutorial

**Release 0.0.1-beta**

**2025-05-25**

**Jiachen Shen**

## Before You Start

Litex is an easy to learn, powerful formal language. Essentially, it is a tool that allows you to write reasoning according to the rules defined by Litex, and Litex will help verify whether your reasoning is correct. As a result, it can be widely used for validating mathematical proofs or any rule-based systems. Litex is basically an attempt to scale and automate reasoning in the AI age.

---  
**Contact:**  
- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com

## Whetting Your Appetite

Everyone have started to think and reason since childhood. The ability to reason is what differentiates humans from other animals. The reason why mathematical reasoning is strict and universal is that it follows a small set of rules so intuitive that it is kind of inherent in human nature. Miraculously, on top of those reasoning rules and another small while carefully selected set of axioms, we human beings are able to build the entire world of mathematics. Since all scientific, engineering, and economic theories are built upon mathematics, the unreasonable effectiveness of those reasoning rules should not be underestimated.

If you are a software developer, or mathematician, or an AI researcher, you might have encountered formal languages. Formal languages are softwares where, people write down their reasoning without breaking the rules of the language, and the software will check if the reasoning are valid accordingly. It works like how a human checks whether a piece of math is correct, but in a more strict and automated way. Just like nobody can calculate faster than a calculator, it can be imagined that nobody can check the validity of reasoning faster than a formal language.

However, traditional formal verification languages like Lean4, Coq, and Isabelle are too complex and too far removed from everyday mathematical notation. These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. If Newton had to learn those theories before inventing calculus, he would never succeed, because those theories would be invented 3 centuries later. The fundamental reason for this complexity is that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system.

Litex is also another formal language, a unique one. It is designed to be simple and intuitive. No brain-exploding theories, no complex syntax, no need to learn a new programming language. All you need to learn before using Litex is building a connection between your own intuition and Litex expressions. Believe me, that is pretty easy. Many mathematical expressions can be translated from natural language to Litex code almost directly.

Maybe you are a young teenager captivated by mathematics, eager to master the art of deductive reasoning and rigorous thinking, just like the ancient philosophers such as Plato or the brilliant detective Sherlock Holmes.

Maybe you are an AI researcher striving to develop reasoning models that can match or surpass human cognitive abilities. Formal mathematical data could enhance your model's reasoning capabilities and perhaps inspire the next breakthrough in model architecture.

Maybe you are a mathematics student seeking to streamline the paper review process, identify potential errors in your thesis, and collaborate with fellow mathematicians online - much like how programmers collaborate through platforms like GitHub.

Maybe you are a rocket scientist who needs absolute certainty in every mathematical formula, ensuring your spacecraft's precise trajectory to the moon.

Maybe you are simply an enthusiast who finds joy in appreciating the elegance of mathematics and discovering how individual concepts intertwine to create a magnificent tapestry of knowledge.

Litex is the perfect language for you. I hope you will enjoy it.

<!-- ## Using The Litex Interpreter, Tools, and Resources -->

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
$intelligent(Jordan) # check whether Jordan is intelligent
```

What the above code means basically is:
- All humans are intelligent.
- Jordan is a human.
- Therefore, Jordan is intelligent. (This is the conclusion)

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

The body of the `know` statement is indented. Indentation is Litex's way of grouping statements. You have to type a tab or spaces for each indented line. You can put as many factual statements as you want in a `know` statement.

Universal Quantification `forall` is a Litex keyword referring to "for all" in math. It means the following statement is true for all objects when parameters all satisfy given conditions. For example, `forall x human: $intelligent(x)` means the factual statement `intelligent(x)` is true for all objects `x` that are members of the set `human`. A factual statement is a statement that is either true or false, and must start with `$`, to differentiate it from a function.

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

To make this tutorial clearer, we will reuse the same example in different contexts. Next time you see `human` or `Jordan` in the examples, you should know that they are the same objects as the ones in the first example.

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
    obj Kobe human # This object is defined in the prove context.
    $intelligent(Kobe)

obj Kobe human # This Kobe is different from the Kobe in the prove context, because it is defined in the main context.
```

`prove` statements opens a new and local proof context. It can see all previous facts in the main context, but it cannot affect it. In this example, the `Kobe` object only exists in the `prove` context, and it is different from the `Kobe` object in the `obj` statement. After leaving the `prove` context, the `Kobe` object will be forgotten. `prove` is used to keep the main context clean and make small drafts.

OK! Let's move on to the detailed explanation of Litex. 

## Specific Facts

<!-- need to say how to define a prop -->

The most fundamental statement in Litex is the `specific` fact. It usually has the following form: a `$` followed by a proposition name, and a list of parameters. For example, `$intelligent(Jordan)` is a specific fact. It tells the Litex interpreter to check whether `$intelligent(Jordan)` is true. 

The validation of a specific fact must satisfy two conditions:

1. Its parameters satisfy the conditions of the proposition, which is written in the `prop` definition statement.
2. There exists a fact in knowledge base that the proposition is true.

For example, if we have already known "$intelligent(Jordan)" in the knowledge base, by `know` statement or is previously proved, then "$intelligent(Jordan)" is verified because 1. Jordan is a human, and 2. Jordan is known to be intelligent, either by a known specific fact or by a known `forall` statement.

The reason why those facts are called `specific` is that they are specific to the parameters. For example, `$intelligent(Jordan)` is specific to the parameter `Jordan`, and `$intelligent(Kobe)` is specific to the parameter `Kobe`. Unlike `forall` statements, which are universal and can be used to generate different facts for different parameters, `specific` facts are specific to the parameters.

Sometimes we want to formalize the opposite of a specific fact. In this case, we put the `not` keyword before the specific fact. For example, `not $intelligent(Jordan)` is the opposite of `$intelligent(Jordan)`.

Not all specific facts are using prefix `$`. For familiarity, some builtin proposition names like `=`, `<`, `>`, `<=`, `>=`, `!=` are infix. For example, you do not write `$=(1+1,2)`, you just write `1+1=2`. Basic arithematic operations like `+`, `-`, `*`, `/`, `^`, `%` are also builtin, and their validation is provided by the Litex interpreter.

The `=` statement is behaves very differently from other specific facts. Objects from any sets can be used as parameter of an `=` statement. And if `x = y` is true, then the validation of  `$P(x)` can immediately lead to the validation of `$P(y)`, because `x = y`, since now x and y are considered to be the same.

Besides, there are also some special features of Litex, all designed to make Litex more like natural language and more aligned with your daily reasoning.

`is` is used when a proposition only takes one parameter. For example, `x is red` is equivalent to `$red(x)`. This is an effort to make Litex more like natural language.

`in` is used when checking whether an object is a member of a set. For example, `$in(x, human)` checks whether `x` is a member of the set `human`.

If a proposition has exactly two parameters, you can put the proposition name infix, with prefix `$`. For example, `x $in human` is equivalent to `$in(x, human)`.

Another group of specific facts are existential facts. They are used to check whether there exists an object that satisfies the condition of the proposition. For example, `exists x st $P(y)` checks whether there exists an object `x` that satisfies the proposition `$P(y)`. We will explain them in later sections.

We can not go far with just specific facts. A specific fact that is true can not tell us anything except itself is true. We need to use `forall` statements to derive new facts from known facts.

## `forall` Statement

`forall` statement, also known as universal quantification, is the building block of the entire of math world. Without it, we cannot can not derive new facts from known facts. They are like using a single finite-length sentence to simultaneously describe countless facts at once.

For example, if we know that `forall x human: $intelligent(x)`, we can conclude that `$intelligent(Jordan)` is true. If Kobe is also a human, we can also conclude that `$intelligent(Kobe)` is true. No matter how many humans there are, we can always conclude that `$intelligent(x)` is true for any human `x`. This is very different from `$intelligent(Jordan)` or `$intelligent(Kobe)`, which are only true for Jordan and Kobe respectively.

### How to write `forall` statements

The body of a `forall` statement is indented and consists of three optional components. Here is an example.

```
# Define some propositions
prop male(x human)
prop man(x human)
prop masculine(x human)

# With extra condition, with iff
forall x human:
    dom:    # dom means domain mathematically
        $male(x)
    then:
        $man(x)
    iff:
        $masculine(x)
```

Three components are:

1. The domain condition (in the `dom` block): This specifies which objects the statement applies to.
2. The conclusion (in the `then` block): This states what must be true for all objects in the domain.
3. The equivalence condition (in the `iff` block): When present, this requires proving that the conclusion and the equivalence condition imply each other within the specified domain.

All three components contain factual statements as body. You can use definition statements like `prop` in the body of a `forall` statement. Three factual statements are:

1. `specific` facts, incluing `exist` statements.
2. `or` statements.
3. `not` statements.

Keep in mind when you are writing `forall` statements inside a `forall` statement, there is an upper limit of the depth, which is 2. This is a guarantee of the interpreter not to go into an infinite loop when searching for related facts.

There are several ways to write `forall` statements in Litex, each serving different purposes:

```
# With extra condition, no iff
forall x human:
    $male(x)
    then:
        $man(x)

# No then condition, just iff
forall x human:
    $male(x)
    iff:
        $man(x)
```

When you don't need a `then` or `iff` block, you can omit them. In such cases, you can also omit the `dom` keyword - the interpreter will automatically treat all statements except the last block as the domain condition. For example, in the above cases, `$male(x)` is automatically treated as the domain of the `forall` statement.

```
forall x human:
    then:
        $intelligent(x)

forall x human:
    iff:
        $intelligent(x)

# No extra condition, no iff
forall x human:
    $intelligent(x)
```

When there is no domain condition, you can write the `then` or `iff` block directly. In fact, when writing a `then` block without a `dom` block, you can even omit the `then` keyword entirely.

## How to verify a factual statement?

Congratulations, you have learned the most basic and important statements in Litex: `forall`, `specific` facts. They are the central blocks of Litex. You are already able to do a lot things with them.

Wait, you might be wondering, how does Litex verify a given fact exactly? Previous examples are pretty straightforward, but how about a more complex example? You might have this feeling that the examples above seem intuitively correct, but you can't quite articulate why they're right.

If Litex has invented anything, it is a language that clearly formalizes the intuitive yet vaguely understood rules of reasoning, making them explicit and precise. The intuition here is that, when we do math, we are constanly using the technique `match and substitute` to derive new facts from known facts.

There are and only are two basic ways of proving a specific fact:

1. By a related known specific fact.
2. By a related known `forall` statement.

By a related known specific fact we mean a known specific fact has exactly the same name as the given specific fact, and their parameters are equal. 

```
prove:
    obj Stephen human
    obj Curry human
    
    know:
        $male(Stephen)
        Stephen = Curry

    $male(Curry) # true, because Stephen = Curry and $male(Stephen) is known.
```

Related messgaes in the output says:

```
$male(Curry)
is true. proved by
$male(Stephen)
Stephen = Curry

---
success! :)
```

As the example above shows, $male(Curry) is true because Stephen = Curry and $male(Stephen) is known. We say Stephen and Curry are matched, and Curry is substituted for Stephen in known fact $male(Stephen). That is why we can conclude that $male(Curry) is true.

Another way of verifying a specific fact is by a known `forall` statement. For example, if we have already known `forall x human: $intelligent(x)`, then we can conclude that `$intelligent(Jordan)` is true because Jordan is a human. There are two, and only two, ways to verify a specific fact: either by a related known specific fact, or by a related known `forall` statement.

Here is a detailed example showing how we use `match and substitute` to verify a specific fact. We can see when `match and substitute` fails and when it is successful.

```
prove:
    set cat
    prop miao(x cat)
    prop physical(x human)
    prop strong(x human)
    prop powerful(x human)

    know：
        forall x cat:
            $miao(x)

        forall x human:
            $intelligent(x)

        forall x human:
            $powerful(x)
            then:
                $strong(x)

        forall x human:
            $physical(x)
            then:
                $strong(x)

        $physical(Jordan)

    # true, because Jordan is a human and $strong(Jordan) is known.
    $strong(Jordan)
```

Related messages in output says:

```
$physical(Jordan)
is true. proved by
$physical(Jordan)
Jordan = Jordan

$strong(Jordan)
is true. proved by
forall `x:
    $physical(`x)
    then:
        $strong(`x)
```

Notice `$strong(Jordan)` is true because 1. Jordan is human 2. `$physical(Jordan)` is true 3. `forall x human: $physical(x) then $strong(x)` is known. It works because the then block `$string(x)` and `$strong(Jordan)` have the same proposition name and therefore can be matched. When matched, Jordan is substituted for x in the then block, and we check whether `$physical(Jordan)` and Jordan is in set human is true. `$physical(Jordan)` is true because it matches the known fact `$physical(Jordan)` and is proved by this specific fact, and Jordan is defined to be in set human when it is defined.

Let's see why other known facts did not help to check `$strong(Jordan)`. `forall x cat: $miao(x)` is known, but it does not help because `miao` and `strong` are different propositions, and also `Jorand` is not known in the set `cat`. `forall x human: $intelligent(x)` does not help to check `$strong(Jordan)` because `intelligent` and `strong` are different propositions. `forall x human: $powerful(x) then $strong(x)` does not help to check `$strong(Jordan)` because `$powerful(Jordan)` is not known.

A `forall` statement is verified slightly differently from a specific fact.

```
prove:
    prop p1(x human)
    prop p2(x human)
    prop p3(x human)

    know:
        forall x human:
        $p1(x) 
        then:
            $p2(x)

        forall x human:
            $p2(x)
            then:
                $p3(x)

    forall x human:
        $p1(x)
        then:
            $p2(x)
            $p3(x)
```

Related messages in output says:

```
forall `x:
    $p1(`x)
    then:
        $p2(`x)
        $p3(`x)
is true
$p1(`x)
is true. proved by
$p1(`x)
`x = `x

$p2(`x)
is true. proved by
forall `x:
    $p1(`x)
    then:
        $p2(`x)
$p2(`x)
is true. proved by
$p2(`x)
`x = `x

$p3(`x)
is true. proved by
forall `x:
    $p2(`x)
    then:
        $p3(`x)
```

The above example wants to prove that `forall x human: $p1(x) then $p2(x) and $p3(x)`. When proving a `forall` statement, Litex will open a new proof context for each object in the domain. In this context, it will put a new object x in the context, x is assumed to be in human set and `$p(x)` is true. Then the `then` block is proved statement by statement. `$p2(x)` is proved by the known fact `forall x human: $p1(x) then $p2(x)`. `$p3(x)` is proved by the known fact `forall x human: $p2(x) then $p3(x)`.

You might be wondering what will happen if most of parameters of the `forall` statements are derived, but not all of them. For example, when using `know forall x human, y human: $p1(x)` to verify `$p1(Jordan)`, we only know `x` in this `forall` statement is subsituted to be `Jordan`. We do not know `y` in this `forall` statement. In this case, this `forall` statment does no help to prove `$p1(Jordan)`. Later, we will introduce `suppose` statement and `with` statement to help you solve this problem.

OK! That is all how verification works in Litex. It is not that hard, right? That is exactly how `match and substitute` works at daily math proof. When a man is verifying a piece of proof, he does `match and substitute` thousands of times in his head, and that is exactly what Litex does. Litex iterates over all possibly related known facts and check whether they can be matched with the body of the given specific fact. If they can, the given specific fact is proved. Do not worry whether Litex is computationally expensive. Litex is very efficient and fast.

Fundamentally, Litex, or math in general, is a fancy game of `match and substitute`. No matter how complicated the proof is, how abstract the problem is, it is just a bunch of `match and substitute` operations at different levels.

## `exist` statement

`exist` statements, also known as existential quantification, is another collection of important factual facts in math in general. It works as the opposite of `forall` statements, since `not forall` means there exists at least one object that satisfies the condition of the `forall` statement but does not satisfy its conclusion.

Here is an example of how to define an existential proposition, verify it, and use it to prove a new fact. 

```
prove:
    obj Kevin human
    obj Durant human

    prop p(x human, y human)
    prop q(x human, y human)

    exist_prop a Human st P(b Human):
        $p(a,b)
        iff:
            $q(a,b)

    know:
        $p(Kevin, Durant)
        $q(Kevin, Durant)

    # true, because $p(Kevin, Durant) is true and $q(Kevin, Durant) is true
    # At the same time, $P(Durant) is also stored in knowledge base
    exist Kevin st $P(Durant)

    # true, because exist Kevin st $P(Durant) is true
    $P(Durant)

    # use have to get a new object of the existential proposition
    have Leonard st $P(Durant)

    # true, because Leonard satisfies $P(Durant) and $q(Leonard, Durant) is consequence of $P(Durant)
    $q(Leonard, Durant)
```

`exist_prop` statement has the form `exist_prop`, a list of existential parameter-set pairs, `st` keyword, a proposition name, and a list of proposition parameters. Notice the existential parameters are not the same as the parameters of the proposition. In the body of the `exist_prop` statement, there are two sections: the domain section and the conclusion section. When the domain section and the conclusion section are both true, the `exist` statement is true. For example, when `$p(Kevin, Durant)` and `$q(Kevin, Durant)` are both true, so `exist Kevin st $P(Durant)` is ture. `exist` statement has the form `exist`, a list of paramters, `st` keyword, a specific fact. When a `exist` statement is true, the specific fact inside (in this case, `$P(Durant)`) is true automatically.

The main use of `exist` statement is by using known `exist` statement to work with `have` statement. `have` statement is a way to introduce new objects into the current context. It has the form `have`, a list of parameters, `st` keyword, a specific fact. In this example, since `$P(Durant)` is true by `exist Kevin st $P(Durant)`, we can use `have` to introduce a new object `Leonard` that satisfies `$P(Durant)`. By definition, since `Leonard` satisfies `$P(Durant)`, so `$q(Leonard, Durant)` is true.

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

## Special Keywords

There are many builtin keywords helping you make reasonings.

`N`, `I`, `F`, `R` are special keywords in Litex. They are used to represent the set of natural numbers, integers, rational numbers (`F` for float), and real numbers respectively.

`frac` is a builtin function that takes in two real numbers and returns a real number (the denominator is not zero). For example, `frac(1,2)` is equivalent to `1/2` in natural language.

`commutative_prop` and `commutative_fn` are special keywords in Litex. When a function is proved to be commutative, when it is being compared with another function, the order of the two functions does not matter. When a proposition is proved to be commutative, the order of the parameters does not matter.

`prove_by_math_induction` is a special keyword in Litex. It is used to prove a statement by mathematical induction.

## Factual Statements

Now you have learned the most basic and important statements in Litex: `forall`, `exist`, `or`, `specific` facts. I hope learning them did not make you lose too much brain cells. They have exactly the same meaning as what you have been using in your daily life. What you just learned is just how to express them in a more formal way in Litex.

You might be wondering, what other factual expressions do I need to know? Are there infinitely many of them? The answer is NO. NO. There are exactly just four of them. YOU CAN BUILD THE ENTIRE WORLD OF MATH WITH JUST FOUR OF THEM. These four keywords are basis of the so called first-order logic statements, and 99.99% of math that you are familiar with are built upon them. Don't let the word "first-order logic" scare you. You have been using it every single day in your daily life, you just need to know the way you are reasoning has this technical name.

**warning: There is a mathematical field called higher-order logic and might be covered in future versions of Litex. It allows you to quantify over propositions, and even over sets. However, most of the math that you are familiar with are built upon first-order logic, with just one exception: the mathematical induction. Don't worry, it is a speical keyword of Litex. If you do not know what high-order logic is, don't worry. It is not the mainstream of math and does not affect your understanding of Litex.**

The core design philosophy of Litex is to make first-order logic accessible and easy to express. Our goal is to create a formal language that is friendly to everyone, not just experts. This is why Litex focuses exclusively on first-order logic - expressed through four key factual statements (forall, exist, or, specific). First-order logic is the most common and essential aspect of mathematical reasoning, and making it accessible to everyone is Litex's primary mission.

Litex is built around first-order logic. After confiirming this as core functionality, the second thing is to add language features (technically, syntax sugar) around it. Litex provides you a rich set of syntax sugar to help them express their reasoning as naturally as possible.

## Function

Functions are very important in math. A function takes in some parameters and returns a value. In Litex, a function works differently from functions in programming languages. There is no execution of a function. Instead, a function works like a symbol which groups together a set of objects and forms a new object.

```
fn f(x R) R:
    x > 0
    then:
        f(x) = x^2

f(2) = 2^2
f(2) = 4
```

In this example, `f` is a function that takes in a real number `x` and returns a real number `f(x)`. The function is defined to be `x^2` when `x` is greater than 0. When we write `f(2) = 2^2`, we are not executing the function `f` with the parameter `2`. Instead, we are saying that `2` is a member of the set `R` and `f(2)` is defined to be `2^2`.

`match and substitute` also works in this example. `f(x) = x^2` is matched by `f(2) = ^2` and `x` is substituted by `2`.

In Litex, basic arithmetic operations are built-in. You can use `+`, `-`, `*`, `/` to add, subtract, multiply, and divide real numbers. `2^2 = 4` is proved automatically without user intervention.

If a function has exactly two parameters, you can put the function name infix, with prefix `\`. For example, `x \add y` is equivalent to `add(x, y)`.

## Set

A set is a collection of objects. In Litex, the parameter list must specify the sets of their parameters. For example, `prop p(x human, y human)` means `p` is a proposition about two human objects. This makes Litex strict and aligned with the set theory.

Unlike types in programming languages, sets in Litex are not a type. An object can be a member of multiple sets. For example, `obj Jordan human` means `Jordan` is defined to be in set `human`. And `know $in(Jordan, basketball_player)` means `Jordan` is defined to be in set `basketball_player`.

## Proof Related Statements

Previously, we have learned `prove` statement. They are used to open a new and local proof context. In this context, you can prove new facts without affecting the main context.

There are several more statements related to proof. `prove_by_contradiction` is used to prove a statement by contradiction. `prove_in_each_case` is used to prove a statement by cases. `prove_or` is used to prove a `or` statement. 

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

```
prove:
    prop p(x I)
    know:
        forall:
            not $p(1)
            not $p(2)
            not $p(3)
            then:
                $p(4)

    prove_or 0,1,2:
        or:
            $p(1)
            $p(2)
            $p(3)
            $p(4)
        prove:
            $p(4)
```

`prove_or` is used to prove a `or` statement. The indexes following `prove_or` are the indexes of the `or` statement that we assume to be false and we want to prove one of the rest of cases in the `or` statement is true. In this example, we assume that `p(0)`, `p(1)`, and `p(2)` are false, and we want to prove that `p(4)` is true. Since we know that `forall: not $p(1) not $p(2) not $p(3) then $p(4)`, we can conclude that `p(4)` is true in this `prove_or` statement.

## `suppose` and `with` Statements

`suppose` statement has the following form:

```
suppose $q(x, y):
    $p(x)
```

It says: first we open a new context. We introduce two new parameters `x` and `y`. We assume `$q(x,y)` is true. In this context, we prove `$p(x)`.

You might be wondering how is it different from `prove` statement. The main funcionality of a `suppose` statement is work together with `with` statement.

```
prove:
    know suppose $q(x, y):
        $p(x)

    know:
        $q(Jordan, Kobe)

    $p(Jordan) # unknown

    with $q(Jordan, Kobe):
        $p(Jordan) # true
``` 

Assume `suppose $q(x, y): $p(x)` is true. (In this case we know it to be true). The `$p(Jordan)` is unknown because despite `suppose $q(x, y): $p(x)` is true in knowledge base, we do not know the `y` in suppose is mapped to be `Kobe`. But when we use `with $q(Jordan, Kobe): $p(Jordan)`, by the `Kobe` in `with $q(Jordan, Kobe)` , we know that `y` is mapped to be `Kobe`, so `$p(Jordan)` is true.

`with` and `suppose` is necessary, because sometimes we do not how to match all the parameters in a forall statement parameter list. In this case, we can use `suppose` to open a new context, just like how a forall statement works and use `with` to match the parameters.

## Words From The Inventor

Hi, I am Jiachen Shen, the creator of Litex. I am a PhD student in mathematics, and I am also a programming language geek. I have been working on Litex since 2024 and received many valuable feedbacks from Litex enthusiasts. I hope you enjoy using Litex, too. 

As a language designer, I have tried very hard to make Litex simple, strict, and intuitive, which requires a lot of thinking, effort. The Unix philosophy "keep it simple, stupid" is the ultimate guideline of Litex design. Every day, I ask the question to myself "what does it mean to be a simple and expressive formal language?". This is a hard question because Litex is so different from other formal languages. I had to figure out the answer to this question all by myself, partly because there are so few people have a good taste in programming language and math at the same time. One can test, debug, and improve in bazaar style, but it would be very hard to originate a project in bazaar style.[^2] Litex indeed has many drawbacks. But I am still proud of it.

In today's highly connected world, there is no project model better than open-source, especially for a fresh project. Now Litex is coming from the stage of originating an idea to the stage of being tested, debugged, and improved by real people. Feel free to contact me if you have any questions or suggestions via [github](https://github.com/litexlang/golitex) and [mail](litexlang@outlook.com). Obviously, Litex is is still in the early stage of development. Any feedbacks are welcome.


[^1]: [Mathematics for Computer Science](https://courses.csail.mit.edu/6.042/spring18/mcs.pdf)

[^2]: [The Cathedral and the Bazaar](https://www.catb.org/esr/writings/cathedral-bazaar/cathedral-bazaar/index.html)