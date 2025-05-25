# The Litex Formal Language Tutorial

**version 0.0.1-beta**

## Whetting Your Appetite

Everyone have started to think and reason since childhood. The ability to reason is what differentiates humans from animals. The reason why mathematical reasoning is strict, undeniable, and universal is that it follows a small set of rules so intuitive that it is kind of inherent in human nature. And miraculously, on top of those rules and another small set of axioms, we human beings are able to build the entire world of mathematics. All scientific, engineering, and economic theories are built upon mathematics.

If you are a software developer, or mathematician, or an AI researcher, you might have encountered formal languages. Formal languages are softwares where, people write down their reasoning without breaking the rules of the language, and the software will check if the reasoning are valid accordingly. It works like how a human checks whether a piece of math is correct, but in a more strict and automated way. Just like nobody can calculate faster than a calculator, nobody can check the validity of a piece of reasoning faster than a formal language. There is huge potential in using formal languages to check the validity of any piece of reasoning.

However, traditional formal languages like Lean4, Coq, Isabelle, etc. are too complex and too far removed from the expression habits of everyday mathematics. For example, these languages are all heavily dependent on type theory and functional programming ,which even math PhD students have to spend years to learn. Techinally, the reason why they are so complicated, is that they both want be a reasoning verifier and a programming language, and keeping a right balance between them is nearly impossible.

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

obj Alice human
$intelligent(Alice) # check whether Alice is self aware
```

What the above code means basically is:
- All humans are self aware.
- Alice is a human.
- Therefore, Alice is self aware. (This is the conclusion)

Let's explain the above code statement by statement.

```
set human
```

Modern mathematics is built upon set theory (Do not worry if you are not familiar with set theory. You will get familiar with it in the future). In Litex, we use `set` to define a set of objects. Here, we define a set of objects called `human`.

```
prop intelligent(x human)
```

`prop` is a Litex keyword referring to "proposition" in math. A proposition is a statement (communication) that is either true or false. Here we define a new proposition called `intelligent`, which is a proposition about an object `x` that is a member of the set `human`. 

Besides `true` and `false`, a proposition can also output `unknown` and `error` in Litex. If an there is no sufficient information to determine the truth value of a proposition, it will output `unknown`. For example, if we do not know whether Alice is a human, the proposition `intelligent(Alice)` will output `unknown`. If the user disobeys the rules of the language, it will output `error`.

```
know:
    forall x human:
        $intelligent(x)
```

Litex Keyword `know` means the following statements are believed to be true by the user. For example, you can use `know` to define a new axiom, make a new assumption, or make a new conclusion. However, be careful when using `know`. If you make a wrong assumption, the whole reasoning process will be invalid.



```
set human 

prop  intelligent(`x)

know:
    forall `x:
        then:
            $intelligent(`x)

obj Alice

$intelligent(Alice)
is true. proved by
forall `x:
    then:
        $intelligent(`x)

---
execution success! :)
```


