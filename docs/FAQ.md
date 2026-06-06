# Litex FAQ

Jiachen Shen and The Litex Team, 2026-06-03. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/FAQ.md

This page collects common questions about Litex's design, performance model,
and intended proof style. It is written as a living note: answers should stay
concrete, modest, and close to the current verifier behavior.

## Why is Litex called Litex?

Litex = Lisp + LaTeX. The author of Litex is inspired by the simplicity and power of Lisp and the practicality of LaTeX.

## How is Litex invented?

By iteratively implementing and refining the Litex language. The design process and implementation process happen side by side. The author took 6000 git commits (mostly before AI becomes sort of usable to help him to do kernel development) to finally know what he is implementing and designing. It's hard to imagine a better way to do something like this. When everything comes together, it's a beautiful thing.

## Is Litex a programming language?

No. Litex is a domain language for and just for mathematics reasoning. It is not a programming language. By sacrificing the programming language features, Litex can focus on the mathematics reasoning features. This is very different from Lean, Coq, and Isabelle. That's why it can be designed as close to ordinary mathematics as possible.

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

## Why does Litex emphasize relationships instead of construction ancestry?

Many familiar mathematical objects can be constructed in more than one way.
Integers can be built from pairs of natural numbers, rationals from pairs of
integers, and reals from Cauchy sequences, Dedekind cuts, decimal expansions,
or other equivalent constructions. Litex does not make ordinary users inherit
all of that construction history every time they write `Z`, `Q`, or `R`.

Instead, Litex is relationship-first. The kernel and standard library expose
common objects and the relationships that make them useful: membership,
arithmetic, order, density, floor bounds, completeness, function spaces, set
operations, and so on. For many day-to-day proofs, the exact construction of
`R` from `Q` is not the point; what matters is that `Q` embeds into `R`,
rationals are dense in reals, Cauchy real sequences converge, and bounded
nonempty real sets have least upper bounds.

This is a deliberate design trade-off. Litex's builtin `R` is a mathematical
surface with verifier-visible properties, not a proof term saying "this object
was constructed by this exact chain of quotients and completions." The standard
library may record facts such as rational density or real completeness with
`know` because, for Litex's default std interpretation, those are trusted
background facts about the standard numeric objects. For example, `std/Rat`
records the reduced numerator/denominator interface for builtin `Q`, while
`std/Real` records the usual real-line relationships. In `std/Real`, the
intended model is the usual real numbers, which can be obtained as the
completion of `Q`; the std file exposes that model through relationship facts
rather than forcing every development to replay the construction.

The practical rule is:

- use builtin objects such as `Z`, `Q`, and `R` directly when the proof only
  needs their ordinary relationships;
- put broad semantic background, such as density of `Q` in `R` or completeness
  of `R`, in the relevant std package and make the trust boundary visible;
- keep chapter-specific or domain-specific theorems local until they are worth
  extracting into a reusable package;
- formalize a construction explicitly only when the construction itself is the
  mathematical subject.

So Litex is not anti-foundational. It simply chooses a lighter user-facing
route for ordinary mathematics: expose the relationships people actually use,
then make any trusted background facts explicit enough to audit.

## What are the boundaries of Litex's type system?

Litex deliberately does not try to be a full dependent type theory in the Lean,
Coq, or Agda sense. Its surface is closer to set-theoretic ordinary
mathematics: objects belong to sets, structures are subsets of Cartesian
products with named views, predicates express properties, and proofs grow a
verified context of facts.

The design keeps some dependent-looking forms because ordinary mathematics
needs them. Later parameter domains may depend on earlier parameters, as in
`fn(c1, c2 q) q`, and `template` supports parameterized families such as
structures, sequence spaces, and quotient constructions indexed by a carrier
or by hypotheses. But Litex does not currently expose general dependent return
types, universe-polymorphic type families, or proof terms as ordinary
computational data. The choice is pragmatic: the project is testing whether a
fact-oriented, readable, set-theoretic interface can cover a large amount of
day-to-day mathematics with a smaller user-facing language.

For a concrete quotient-group construction, see the quotient-group section in
the Manual.

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

A useful way to read a template is: first pretend that the angle-bracket
parameters have already been introduced and satisfy the header conditions.
Then run the statements inside the template body as ordinary definition
statements in that temporary context. If those statements check, Litex stores
the result as a family. When you later write an instance such as `\name<R>`,
Litex substitutes the concrete argument for the parameter and gives you the
corresponding defined object or function.

For example:

```litex
template<s set>:
    have carrier_copy set = s

\carrier_copy<R> = R
\carrier_copy<Z> = Z
```

The reading is: first fix an arbitrary set `s`; in that temporary context,
`carrier_copy` is definable as `s`; because this works for every `s set`, the
family can later be called as `\carrier_copy<R>`, `\carrier_copy<Z>`, and so on.

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

No. `know` is explicit assumption injection, not a proof-producing command. It
adds a fact to the current context after checking that the statement is
meaningful enough to store. Later checked facts may depend on it.

The name can be misleading if read informally. In documentation and audits,
read `know P` as "assume P from this point onward." If a later `verified_by`
trace cites a fact that came from `know`, the trace explains why the later line
follows from the injected assumption; it does not show that the injected
assumption was proved by Litex.

Likewise, `result: "success"` on a `KnowStmt` only means the assumption was
accepted into the context. It is not a certificate that the injected fact was
proved.

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

## Research Positioning

Litex is not trying to replace Lean, Coq, or Isabelle. It tests whether a
readable, fact-oriented surface language, backed by a larger trusted
mathematical checker, can make useful checked mathematics cheaper for students,
domain scientists, and AI agents.

## Litex Vs Lean

Lean is the stronger mature ecosystem, with Mathlib, tactics, proof terms, and
a small trusted kernel. Litex explores a different interface: users write
mathematical facts in order, and the checker grows an explainable context by
matching shapes, known facts, known `forall` facts, builtin rules, and inferred
facts.

## AI For Science

Litex is useful where a scientific or applied derivation already has local
claims that should be checked, repaired, or audited. The goal is not to certify
discovery by prose, but to put generated derivations into a fast verifier
feedback loop.

## For Mathematicians

For mathematicians, the main point is that Litex can start from objects,
functions, predicates, axioms, and reusable definitions before choosing a
concrete model. This fits quotient-style constructions, axiomatic structures,
set interfaces, and algebraic proof flows.

## Soundness And Limitations

A Litex success is relative to the trusted background. `know` is explicit
assumption injection, similar in role to Lean's `by sorry`: it adds facts to the
context without proving them. `abstract_prop` declares an uninterpreted
predicate name and gives it no mathematical content by itself. In final
artifacts, each use should be replaced by a checked claim/theorem, justified as
trusted background, or recorded as remaining proof debt.

## Verifier Flow Examples

The verifier pipeline has three different kinds of outcomes that should not be
confused: proof-required facts that must verify, executor statements that update
the environment, and store/assume-only paths such as `know` or local
assumptions. The detailed reference belongs in the Manual's proof-process
section.

## Preview Features

Preview features should be documented in the Manual when they are part of the
current language surface. Features that are too unstable for the Manual should
stay in code comments, examples, or issue notes until their behavior is clear.

## Litex Cheatsheet

Quick syntax reminders are useful, but they should not become a second reference
manual. New users should start with `have`, bare fact lines, `forall`, `claim`,
`witness`, and `by cases`; use `know` and `abstract_prop` only when
intentionally modeling axioms or proof debt.

## Tutorial Introduction

The beginner path is: write a tiny checked fact, add context, define a concept,
use a local proof block, and read `true`, `unknown`, and `error` as feedback.
The Manual carries the durable version of this learning path.

## Tutorial Examples

Small examples are still valuable, but they should live as runnable `.lit` files
or short Manual snippets rather than a separate prose page that can drift from
the language reference.

## Hilbert Axioms Of Euclidean Geometry

The Hilbert geometry example demonstrated abstraction-first development:
declare primitive objects and relations, record axioms explicitly, then build
derived notions on top. The same lesson applies to any axiomatic interface where
the structure should be visible before a concrete model is chosen.

## How Litex Proves A Fact

Litex proves a fact by trying proof routes such as builtin rules, known facts,
known `forall` facts, prop definitions, and theorem calls. Those details belong
in the Manual because they describe language behavior, not positioning.

## How To Contribute

Useful contribution work should be evidence-driven: translate small
representative mathematical slices, run the verifier, keep successful items
runnable, and record blockers precisely.

## Dataset Contributor Flow

Dataset work should keep a tight loop: understand the math, write natural
Litex, run the verifier, classify the result as translated/checkable/blocked,
and record the blocker when the proof cannot yet be completed.

## Benchmarks And Case Studies

Benchmark claims should come from runnable artifacts, not positioning text.
Failed translations are useful data when they identify missing language, stdlib,
inference, kernel, or diagnostic support.

## Reviewer Guide

Review Litex by separating the interface hypothesis from trust-boundary risks.
A proof script can be readable and promising while builtin rules, `know`, stdlib
coverage, and dataset bookkeeping still need careful audit.
