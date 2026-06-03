# Litex FAQ

Jiachen Shen and The Litex Team, 2026-06-03. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/FAQ.md

This page collects common questions about Litex's design, performance model,
and intended proof style. It is written as a living note: answers should stay
concrete, modest, and close to the current verifier behavior.

## If there are ten thousand `forall` facts, will proving one proposition become slow?

It can become slow if all ten thousand universal facts are active automatic
matching candidates in the same context. Litex's proof model uses known facts,
builtin rules, substitution, and known `forall` facts to justify later facts.
That is useful because users can write the mathematical fact they want, but it
also means the active context should not be treated as an unbounded global
search space.

There are two main design answers.

First, use `thm` for named theorems that should be called explicitly. A
`thm` proves and stores a named theorem, but it does not add its `forall` body
as an ordinary automatic `forall` matching fact. To use it, the proof says
`by thm name(args...)`. That makes large, classic, expensive, or
parameter-sensitive results explicit proof dependencies instead of background
noise.

Second, organize broad mathematical background into packages. A theorem about
groups should live in a group-related package; a theorem about real analysis
should live in a real-analysis package. The user imports the package when that
background is actually needed. This keeps the active known-fact and known-`forall`
space closer to the topic of the current proof.

A practical rule of thumb is:

- use automatic `forall` matching for short, local, common facts whose intended
  instantiation is obvious from the goal shape;
- use `claim forall` or direct `forall` facts when you want a helper to behave
  like local reusable context;
- use `thm` plus `by thm` when the theorem name and arguments should be visible
  in the proof;
- split standard-library facts by subject and import only the subjects needed
  for the current file.

This is not only a performance issue. It is also proof readability. If a fact
is mathematically important, the proof is often clearer when it names that fact
directly.

## What is a type in Litex?

In Litex, "type" is mostly a set-theoretic parameter annotation, not a type in
dependent type theory.

When a user writes `have x R`, `forall x R:`, or `exist x R st { ... }`, the
annotation `R` means that `x` is an object with the membership fact `x $in R`.
The same idea applies to `Z`, `N`, `{1, 2, 3}`, `cart(R, Z)`, `power_set(S)`,
and other ordinary set objects. The annotation gives Litex well-definedness
information and a fact that later proof steps can match.

Some annotations are parameter kinds rather than ordinary set domains. For
example, `have A set`, `have B nonempty_set`, and `have C finite_set` introduce
names and record facts such as `$is_set(A)`, `$is_nonempty_set(B)`, and
`$is_finite_set(C)`. These are not meant to say that `set` is one giant set
containing all sets. They are surface forms for introducing mathematical
objects with the corresponding set-theoretic properties.

Function "types" are also set-theoretic function spaces. A declaration such as
`fn(x S) T` means a function object whose inputs come from `S` and whose values
come from `T`. The domain and return set are ordinary set objects; broader
parameter kinds such as `set`, `nonempty_set`, and `finite_set` belong in
definition or theorem headers, not as ordinary function input domains. This is
why `fn(x set) R` is not the right way to say "a function that accepts any
set." Set-theoretic functions must have one concrete domain object, and Litex
does not treat "the collection of all sets" as one ordinary set object.

This has an important consequence: a Litex object does not have one unique
canonical type that determines all later notation. The same object may be known
to belong to several sets. Litex uses the currently verified membership,
function-space, and set-property facts to decide whether expressions are
well-defined and whether later facts can be proved.

## What is a `struct` in Litex?

A `struct` is not a class or a record object with hidden fields. It is a named
view of a subset of a Cartesian product. The field names label the positions in
that product.

For example:

```litex
struct FirstQuadrant:
    x R
    y R
    <=>:
        x > 0
        y > 0
```

Read this as a named set-builder over `cart(R, R)`:

```text
&FirstQuadrant = { p in cart(R, R) | p[1] > 0 and p[2] > 0 }
```

Here the field name `x` labels index `1`, and `y` labels index `2`. So
`&FirstQuadrant{p}.x` means: first view `p` as an element of
`&FirstQuadrant`, then take the component labeled by `x`, namely `p[1]`.
Similarly, `&FirstQuadrant{p}.y` means `p[2]`.

For a parameterized struct, `&Name<a>` is the instantiated struct set. For a
non-parameterized struct, `&Name` is the struct set. In both cases, the object
inside braces is the underlying tuple-like element being viewed through that
struct.

The explicit prefix is intentional. The same tuple may belong to several
struct sets, and the same field name may refer to different indices in
different struct views.

## Why can an anonymous function be written as `'R(x){-x}`?

This is intentional shorthand, not a typo. The fully explicit anonymous
function form is `'(x R) R { -x }`: the parameter `x` ranges over `R`, the
return set is `R`, and the body is `-x`.

When all parameters have the same domain as the return set, Litex also accepts
the compact form `'R(x){-x}`. Similarly, `'R(x, y){x + y}` means that both
inputs range over `R` and the return set is `R`; it is the compact version of
`'(x R, y R) R { x + y }`.

The compact form is useful in short mathematical expressions, such as passing
`'R(x){x}` to a sum or using `'R(x){-x}` as a group inverse operation. In
explanatory documentation or when the domain and return set are easy to
confuse, the explicit form is usually clearer. Both forms denote ordinary
anonymous function objects and can be compared by Litex's function-equality
rules.

## Why does Litex have `template`?

`template` is the mechanism for definitions that are uniform in a parameter
such as a set, a structure, or a carrier satisfying some condition, when that
parameter cannot be modeled as the input of one ordinary set-theoretic function.

The simplest reason is the one above: a Litex function input must range over a
particular domain set. But `set` is not itself a particular domain set. It is a
surface parameter kind meaning "introduce a parameter and check that it is a
set." So a family defined for every set should carry that set in the definition
header, not hide it as a fake function argument.

A template instance keeps its parameters visible in angle brackets. If a family
is defined as `template<s set>:` with body `have name ...`, then the instance at
`R` is written like `\name<R>`, and the instance at `Z` is written like
`\name<Z>`. The chosen set travels with the name. This is useful because every
use shows which carrier or parameter the object belongs to, and different
instances cannot be confused.

This pattern appears throughout ordinary mathematics:

- `seq(S)` is conceptually a family indexed by the value set `S`; a sequence
  over `S` is essentially a function from positive integers into `S`, not one
  universal function type over all possible value sets.
- A group structure is a family over a carrier set. `&Group<R>` and
  `&Group<Z>` are different struct views because the carrier set is part of the
  mathematical data.
- A quotient construction is naturally a family over a concrete group together
  with the relevant normality or equivalence assumptions. The quotient is not
  one global function from "all groups" to sets; it is a parameterized
  construction whose parameters should remain visible.

This is the point of `template`: it gives Litex a direct way to express
mathematical families while staying set-theoretic. Ordinary functions are for
maps whose domain is a known set. Templates are for families indexed by
mathematical parameters that should stay attached to each instance.

For example, `seq` is a built-in object form in Litex, but if we wanted to
define the same idea ourselves, we would define a family of function spaces:

```litex
template<S set>:
    have my_seq set = fn(n N_pos) S

\my_seq<R> = fn(n N_pos) R

have a fn(n N_pos) R
a $in \my_seq<R>
```

The important point is that `S` is not an ordinary function input. It is a
parameter of the family. After instantiation, `\my_seq<R>` is the ordinary set
of real-valued sequences, namely functions from `N_pos` to `R`. Similarly,
`\my_seq<Z>` would be the set of integer-valued sequences. The angle-bracket
argument keeps the value set visible at every use.

The built-in `seq(S)` can still have special syntax or verifier support. The
template version shows the underlying set-theoretic shape: a sequence type is a
parameterized family of function spaces.

## What is fundamentally different about Litex?

Litex's core difference is its matching-and-substitution verification
interface.

The user writes mathematical facts: equalities, memberships, implications,
existential witnesses, `forall` statements, function facts, set facts, and
predicate facts. The verifier then asks whether the new fact follows from the
current verified context by builtin rules, known facts, known `forall` facts,
definitions, matching, and substitution.

So the central interaction is not "choose a tactic that transforms the proof
state." It is closer to:

1. write the next mathematical fact;
2. let Litex match it against the verified context and trusted mathematical
   background;
3. if it succeeds, store the fact and continue growing the context;
4. if it fails, inspect whether the missing step is a missing fact, missing
   theorem call, missing library support, or a real gap in the argument.

This is why Litex proofs often look like ordinary mathematical prose or
calculation chains. The proof script exposes the facts that should be true, and
the checker performs routine matching and replacement steps that a human reader
would usually do silently.

This does not mean Litex proves arbitrary goals by magic. It means Litex places
more ordinary mathematical structure inside the verifier and standard library,
then gives the user a fact-oriented interface to that structure. The trade-off
is explicit: Litex has a larger trusted implementation than a small-kernel proof
assistant, so builtin rules, infer rules, `know`, and standard-library facts
need clear boundaries, tests, and audit-friendly output.

Litex should therefore be described as complementary to Lean, Coq, and Isabelle,
not a replacement for them. Those systems expose deeper foundations and much
larger mature libraries. Litex tests a narrower hypothesis: many ordinary
mathematical arguments may become cheaper to check if the main proof interface
is verified context growth through matching and substitution.

## Why translate Tao Analysis with Litex builtins instead of rebuilding the foundations?

For Tao Analysis translation, the main target is a verifiable analysis library,
not a faithful reconstruction of every foundational construction in the book.
Litex gives users basic mathematical objects such as `N`, `Z`, `Q`, `R`, sets,
membership, subsets, finite sets, tuples, Cartesian products, functions, order,
and equality as builtin or standard-library interfaces. Translation work should
use those interfaces when they express the intended mathematics.

This is a deliberate design choice. Tao's constructions of integers, rationals,
and reals are mathematically valuable, but they are not the only possible
constructions of those objects. Different constructions can produce structures
with the same ordinary relationships needed for analysis. Litex's surface
language is not organized as a user-visible rebuild from foundational layers;
it treats those basic objects and relationships as part of the shared
mathematical background that must be documented, tested, and audited.

The chapter coverage still matters. A Tao-facing definition or theorem should
remain traceable in the chapter file when it matters for source coverage, and a
constructive proof route can be kept as a proof sketch, local proof debt, or a
future standard-library task. But the checked main route should use the
Litex-native object or theorem when it exists. In Chapters 3-5, this means that
set axioms, integer/rational constructions, and the Cauchy quotient
construction of the reals guide proof debt and API design; they do not block
the main analysis library from using builtin/std `N`, `Z`, `Q`, and `R`.

For Chapter 5 specifically, the intended policy is bridge-only. Litex should
not build a new first-class quotient/completion type just to mirror Tao's
construction of the reals. It is enough to keep source-traceable bridge facts:
rational Cauchy sequences can have formal limits in builtin `R`, every builtin
real can be represented by such a sequence, and equivalent representatives with
formal limits determine the same real. Product, reciprocal, and
bounded-away-from-zero estimates are useful rational Cauchy-sequence algebra
lemmas, but they are not prerequisites for constructing `R`.

## Why does Litex think of proof as context growth?

Litex's proof interface is fact-oriented. A proof is usually written as a
sequence of mathematical facts. When a fact is verified, Litex stores it in the
current context, and later facts may use it by matching, substitution, builtin
rules, or known `forall` instantiation.

For example:

```litex
have x R = 2
x + 1 = 3
```

The second line is not a tactic script. It is the mathematical fact the user
wants. Litex checks that `x` is known to be `2`, reduces the equality to an
ordinary numeric calculation, and then stores the new fact. This is the core
reader experience: write the next useful fact, let the checker explain why it
follows, then continue from the stronger context.

## Why does Litex distinguish `true`, `unknown`, and `error`?

The three statuses separate three different situations that are easy to
confuse.

`true` means Litex found a proof route from builtin rules, known facts, known
`forall` facts, definitions, or other accepted context. `unknown` means the
statement is meaningful, but Litex did not find enough information to prove it.
The statement may be false, or it may only need a smaller intermediate step.
`error` means the statement is not a valid checkable fact yet, for example
because the syntax is wrong, a name is undeclared, or an expression is not
well-defined.

This makes the feedback loop more useful. An `unknown` result usually suggests
"add the missing mathematical fact." An `error` result suggests "fix the
expression or its domain information before discussing truth."

## Why does Litex check well-definedness before truth?

Litex treats mathematical expressions as meaningful only when their objects,
domains, and side conditions are justified. This happens before the checker
tries to prove or disprove the fact.

For example, a function application must have an argument in the function's
domain, and a division must have a nonzero denominator. If those facts are not
available, Litex should report a problem with the expression, not merely say
that the desired equality is `unknown`.

This design matters because many mathematical mistakes are not false theorems
but ill-formed statements: applying a function outside its domain, using a
projection from the wrong Cartesian product, or writing an expression with a
missing side condition. Litex tries to make that distinction explicit.

## Why does Litex have both `claim` and `thm`?

`claim` and `thm` both prove facts, but they have different proof-interface
roles.

A `claim` is good for short, local, reusable context. After it is proved, its
fact is available to later lines in the ordinary context. This is useful for
helper facts that should behave like part of the current mathematical
environment.

A `thm` is good for important named results whose use should be visible. A
theorem is stored under a name and used explicitly with `by thm name(args...)`.
This keeps large, classic, parameter-sensitive, or standard-library results
from silently becoming background search noise.

The distinction is partly about performance, but mostly about readability.
When a result is mathematically important, naming the theorem at the use site
often makes the proof easier to audit.

## Is `know` a proof?

No. `know` is not a proof-producing command. It adds a fact to the current
context after checking that the statement is meaningful enough to store. Later
checked facts may depend on it.

This is useful for three narrow purposes:

- introducing background assumptions in a small example;
- marking exact proof debt while translating or experimenting;
- temporarily stating a theorem or library fact that should later become a
  checked `claim`, `thm`, builtin rule, or standard-library result.

The cost is explicit. If a false statement is introduced with `know`, later
results can inherit that assumption. Serious Litex developments should keep
remaining `know` facts visible and treat them as assumptions or proof debt, not
as completed proof.

## Why does Litex infer extra facts after accepting a line?

Some mathematical facts carry routine consequences. Litex stores those
consequences so the user does not have to restate every projection, membership,
domain fact, or set-builder condition by hand.

For example, after Litex knows that an object belongs to a struct set, it can
store facts about the corresponding tuple components and explicit struct-field
views. After it knows a function object and a valid input, it can use the
function's domain and return-set information. After it records certain set or
Cartesian-product facts, it can infer basic membership and projection facts.

This is one reason Litex proofs can stay close to ordinary mathematical prose.
The user states the meaningful structural fact once, and the checker records
the small consequences that a human reader would normally keep in mind.

## Why does `have by exist` name witnesses explicitly?

An existential fact says that some object exists. A later proof often needs to
choose a name for such an object and use its properties. `have by exist` is the
Litex form of that ordinary mathematical move.

For example:

```litex
know exist u R st {u > 0, u < 1}
have by exist v R st {v > 0, v < 1}: w
w > 0
```

The first line records an existential fact. The `have by exist` line introduces
the witness name `w` for a matching existential statement. After that, the
witness properties are available in the context.

The design keeps the difference clear: the existential statement itself is a
fact, while the witness name is a local object introduced for the current
argument.

## What are `fn_range` and `have by preimage` for?

`fn_range(f)` is the set of values reached by a function `f`. If Litex knows
that a value is in this range, then ordinary mathematics allows us to choose a
preimage. `have by preimage` turns that move into an explicit proof step.

For example:

```litex
prove:
    have f fn(x R: x > 0) R

    f(1) $in fn_range(f)
    have by preimage x from f(1) $in fn_range(f)

    x $in R
    x > 0
    f(1) = f(x)
```

For multi-argument functions, one preimage name is provided for each function
parameter. This feature is small but important: it makes "since this value is
in the range, take a point mapping to it" a checkable, named move rather than
an implicit jump.

## Why does Litex have `stop import`?

Imports add useful facts, theorems, and proof routes. But a large imported
module can also make automatic search harder to understand. `stop import Name`
keeps the module registered while removing it from ordinary automatic
verification.

This lets users control the active proof environment. A stopped module can
still be cited explicitly, for example with a named theorem call, but its facts
do not silently participate in every later search.

The point is not only speed. It is auditability. If a proof depends on a large
external result, the proof is often clearer when that dependency appears as an
explicit citation instead of an invisible background match.

## What is `strategy` for?

`strategy` is for proof patterns where the hard part is not the outer
predicate name, but the internal structure of the object being checked.
Ordinary `forall` matching is intentionally shallow: it can apply a stored rule
when the goal shape matches, but it should not blindly search through every
subexpression of a large object. Deep search would be expensive and hard to
audit.

This matters for predicates that also serve as practical well-definedness
interfaces. Suppose `f`, `g`, `h`, and `t` are known to have a property such as
being differentiable or integrable, and the library knows that this property is
closed under pointwise addition, subtraction, and multiplication. For a nested
anonymous function such as:

```text
'R(x R){f(x) + (g(x) - h(x)) * t(x)}
```

without a strategy, the user may have to introduce the intermediate pieces by
hand: first `g - h`, then `(g - h) * t`, then the final sum with `f`. The proof
is mathematically routine, but the object is syntactically deep.

A `strategy` lets Litex attach a dedicated proof route to the target predicate
shape, so this kind of structural proof can be handled in a controlled place
instead of being baked into unrestricted global `forall` search. In other
words, a strategy is not just "more automation"; it is a scoped way to teach
Litex how to descend into a particular family of objects when proving a
particular predicate.

The shape is:

```text
strategy name:
    prove:
        forall parameters:
            assumptions
            =>:
                $target_predicate(...)
```

After the strategy is registered, Litex can use it when it sees a matching
predicate goal. The strategy can also be stopped and re-enabled, so this form
of automation remains local and controllable. In serious files, a strategy
should be backed by a real checked proof or by clearly marked proof debt, just
like any other reusable proof route.
