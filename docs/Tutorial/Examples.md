# Litex Tutorial: Examples

Jiachen Shen and The Litex Team, 2026-05-21. Email: litexlang@outlook.com

Read the explanation first:

- https://litexlang.com/doc/Tutorial/Explanations

Try these in browser:

- https://litexlang.com/doc/Tutorial/Examples
- https://litexlang.com/doc/Manual

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Tutorial/Examples.md

## Example 1: A Bare Fact

```litex
1 + 1 = 2
```

This is the smallest Litex program that already does something real: it states a fact, and Litex checks it.

## Example 2: Introduce a Value

```litex
have x R = 2
x = 2
```

The first line introduces `x` and fixes its value.  
The second line is then easy to verify because the context already contains `x = 2`.

## Example 3: Reuse Known Value

```litex
have x R = 2
x + 1 = 3
x^2 = 4
```

This is the first example that feels like Litex:

- you state one value,
- then reuse it in later facts.

## Example 4: Store a Fact With `know`

```litex
abstract_prop some_property(x)
have a R = 2
know $some_property(a)
$some_property(2)
```

`know` stores the fact in the context.  
The second line shows that the fact is now available.

## Example 5: Membership

```litex
1 $in {1, 2, 3}
```

Litex can verify many simple set-membership facts directly.

## Example 6: A Simple `forall`

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
```

This is a general fact:

- assume `x` is a real number,
- assume `x = 2`,
- then prove `x + 1 = 3`.

## Example 7: Reuse a Known `forall`

```litex
know forall x R:
    x = 2
    =>:
        x + 1 = 3

have a R = 2
a + 1 = 3
```

This is one of the most important Litex patterns.

The known `forall` acts like a reusable theorem.  
When Litex sees `a = 2`, it can instantiate the theorem with `a`.

## Example 8: Two Conclusions Under One Assumption

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

The block under `=>:` is checked in the local context where `x = 2`.

## Example 9: A User Predicate

```litex
abstract_prop mortal(x)

know forall x R:
    x = 1
    =>:
        $mortal(x)

have Socrates R = 1
$mortal(Socrates)
```

This shows the shape of logical reuse:

- define a predicate symbol,
- store a general fact,
- instantiate it later.

## Example 10: Existential Witness

```litex
witness exist x R st {x > 0, x < 1} from 0.5
```

This means:

- we want to prove there exists a real `x`
- such that `x > 0` and `x < 1`
- and we choose `0.5` as the witness

## Example 11: A Small Proof Flow

```litex
have a R = 5
have b R = a + 1
b = 6
```

This is a good model for many beginner scripts:

1. introduce an object,
2. define another object from it,
3. ask Litex to verify a concrete consequence.

## Example 12: What an `unknown` Usually Feels Like

```text
have x R
x + 1 = 3
```

The output looks like this:

```text
{
  "error_type": "VerifyError",
  "result": "error",
  "line": 2,
  "message": "verification failed",
  "type": "AtomicFact",
  "stmt": "x + 1 = 3",
  "previous_error":
  {
    "error_type": "UnknownError",
    "result": "error",
    "line": 2,
    "message": "",
    "type": "AtomicFact",
    "stmt": "x + 1 = 3",
    "previous_error": null
  }
}

```

Here Litex usually cannot prove the second line, because `x` has been introduced but not fixed.

This is a useful lesson:

- introducing an object is not the same as giving enough information about it.

## Example 13: Fix the Missing Assumption

```litex
have x R = 2
x + 1 = 3
```

Now the proof can go through because the missing fact was added.

## Example 14: Read Litex in Mathematical Order

```litex
have x R = 3
have y R = x + 2
y = 5
y > x
```

This is the recommended reading order for Litex in general:

- first introduce the objects,
- then state the local facts,
- then ask for the consequences you care about.

## A Good First Habit

When writing Litex for the first time, try this rule:

> Do not jump directly to the final line.  
> First write the facts that a human would naturally say out loud.

That style usually works much better than trying to be clever.

## What To Do Next

After these examples, go to:

- Mechanics of Litex Proof: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Examples
- Manual: https://litexlang.com/doc/Manual