# Litex FAQ

Jiachen Shen and The Litex Team, 2026-06-03. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/FAQ.md

This page collects common questions about Litex's design, performance model,
and intended proof style. It is written as a living note: answers should stay
concrete, modest, and close to the current verifier behavior.

Litex source code stays the same across languages, but CLI output supports
localized JSON keys and explanatory labels with `litex -lang <code> ...`.
See [`docs/cli.md`](cli.md) for the supported language codes.

## Why is Litex called Litex?

Litex = Lisp + LaTeX. 

Litex is inspired by Lisp not only in the idea “data
as code,” but also in its taste for a small uniform
core, symbolic manipulation, tree-shaped programs,
interactive feedback, and language-building through
small composable forms.

Litex is inspired by LaTeX's practical design for writing mathematics.

## Does Litex support multiple output languages?

Yes. Use `litex -lang <code> ...` to localize JSON keys and explanatory labels.
The proof script inside fields such as `statement`, `fact`, and
`cited_statement` remains ordinary Litex code. Supported codes include `en`,
`zh`, `zh-Hans`, `ja`, `ko`, `es`, `fr`, `de`, `pt`, `ru`, `ar`, `hi`, `vi`,
and `id`.

## How is Litex invented?

By iteratively implementing and refining the Litex language. The design process and implementation process happen side by side. The author took 6000 git commits (mostly before AI becomes sort of usable to help him to do kernel development) to finally know what he is implementing and designing. It's hard to imagine a better way to do something like this. When everything comes together, it's a beautiful thing.

## Is Litex a programming language?

No. Litex is a domain language for and just for mathematics reasoning. It is not a programming language. By sacrificing the programming language features, Litex can focus on the mathematics reasoning features. This is very different from Lean, Coq, and Isabelle. That's why it can be designed as close to ordinary mathematics as possible.

## Where does features of Litex come from?

The features of Litex come from the author's experience in writing mathematics. The author has been writing mathematics for a long time, and he has some understanding of the mathematics reasoning process. The author has also been writing code for a long time, and he has some understanding of the code reasoning process. He thinks formal language should be used by everyone, just like math is used by everyone.

Most of the features of Litex come from the author's experience in writing mathematics and code. The core verification process `match and substitute` is inspired by how people verify a fact: When he sees a fact not yet proven, he will try to match the fact with a known fact, and if the match is successful, he will substitute the arguments of the known fact into the fact to be proven. If it's ok to substitute, then the fact is proven.

`template` of Litex is inspired by the `template` of C++ (some math object can be defined on different sets)and `interface` of Go (The parameters of template must satisfy certain properties)

`struct` of Litex is inspired by the `struct` of C.

`claim`, `thm` of Litex is inspired by what `theorem` means in math books.

`strategy` and builtin rules of Litex is inspired by how people verify the well-definedness of a recursively defined object.

Syntax sugar of `xxx set` in `forall xxx set` meaning `$is_set(xxx)` is inspired by the discovery that when we talk about sets, we almost always are saying that `something is a set`. So the word `set` never appear independently in the language. It always shows up together with `<some_object> is a set`.

Anonymous function syntax like`'(x R) R {-x}` is essential because they are used as parameters of functions like `sum` and `product` and `\integral`. It's inspired by JavaScript's `(x) => -x` syntax.

The correlation between `tuple` and `cart` and `struct` is essential, because anything, including `struct`, must correlate to something in set theory. Nothing in Litex should be arbitrary and without any concrete mathematical meaning. By viewing one object as a struct, we can use something like `&Point<R, R>((0,0)).x` to view tuple `(0,0)` as a point in the plane `R x R` and get its first coordinate by `.x`.

## What does "Litex is built on relationships between objects instead of meanings of them"



Object `Q` (real numbers) can be defined by algebraic extension of `Z`, or it can be defined in other ways, but Litex does not builtin that. Litex allows the user to choose what axiom system he is using. Similarly, a function `f fn(x R, y R)R` can be viewed as a subset of `cart(R, R, R)` or `cart(cart(R, R), R)`, both are reasonable and Litex also does not support that and the user himself can use `know` keyword to choose which definition he prefers. On the other hand, the properties of `Q`, `fn(x R, y R)R` are builtin, like `all integers are in Q`, so despite not having its definition, we can still use them conveniently.

When we were learning Euclidean geometry in middle school, our teachers would say that these so-called points, lines, planes, and circles are not actually the real ones we draw on paper. They are imagined constructs that possess specific properties. What they fundamentally are is not important; what matters is that there are certain axioms governing these objects, which form the relationships among them. Although they can be defined by using more abstract math concepts (using cartesian coordinate for example), we don't consider that since we only want to focus on properties like parallel and intersection, which those axioms already can process. Similarly, real numbers, rational numbers, and the like can also be defined using more abstract mathematical concepts—users can construct these definitions themselves using Litex code. In fact, however, what is even more important is the relationships between them, and this is precisely what Litex emphasizes.

Read the content from Terrence Tao's Analysis One:

```

Remark 2.1.14. Note that our definition of the natural numbers is ax- iomatic rather than constructive. We have not told you what the natural numbers are (so we do not address such questions as what the numbers are made of, are they physical objects, what do they measure, etc.) - we have only listed some things you can do with them (in fact, the only operation we have defined on them right now is the increment one) and some of the properties that they have. This is how mathematics works - it treats its objects abstractly, caring only about what properties the objects have, not what the objects are or what they mean. If one wants to do mathematics, it does not matter whether a natural number means a certain arrangement of beads on an abacus, or a certain organization of bits in a computer’s memory, or some more abstract concept with no physical substance; as long as you can increment them, see if two of them are equal, and later on do other arithmetic operations such as add and multiply, they qualify as numbers for mathematical purposes (provided they obey the requisite axioms, of course). It is possible to construct the natural numbers from other mathematical objects - from sets, for instance - but there are multiple ways to construct a working model of the natural numbers, and it is pointless, at least from a mathematician’s standpoint, as to argue about which model is the “true” one - as long as it obeys all the axioms and does all the right things, that’s good enough to do maths.

```

As far as Litex is concerned, Litex contains and only contains standard math properties.

## Why does Litex have this particular menu of objects and statements?

Litex's grammar is intentionally finite and opinionated. The goal is not to
let every possible proof-engine concept become a new surface form. The goal is
to keep a small set of object and statement forms that make ordinary
mathematical writing comfortable while remaining checkable.

There are two main reasons a form becomes first-class.

First, some forms are basic mathematical or logical infrastructure. Equality,
membership, number literals, arithmetic, function application, `forall`,
`exist`, conjunction, cases, witnesses, definitions, and proof blocks are
trusted background, logical organization, or computational material that the
verifier needs to understand directly. If these were only encoded through a
more remote abstraction, nearly every proof would spend its budget on
bookkeeping before reaching the mathematical idea.

Second, some forms are user-interface choices. They are included because
mathematicians already write them, often with a close LaTeX analogue: set
displays, tuples, Cartesian products, intervals, sums, anonymous functions,
chained equalities or inequalities, `have`, `claim`, `witness`, `by cases`,
and similar proof moves. These forms are not all foundationally primitive in
the same sense. They are there because they make Litex code feel familiar and
reduce the distance between a paper proof and a checked script.

So `obj` and `statement` in Litex are a design boundary. Objects are the
mathematical expressions facts can talk about. Statements are the actions that
introduce objects, define vocabulary, assert facts, and organize proofs. A new
object or statement form has to earn its place: either the checker needs it as
direct mathematical background, or it makes the user-facing mathematical
surface substantially clearer.

This is one of Litex's unusual design choices. It optimizes for user comfort
and mathematical familiarity with as few first-class forms as possible, rather
than starting from a maximally general programming language or proof-term
calculus.

## What are builtin objects, builtin facts, and builtin rules?

Litex is easiest to understand through four related layers:

- an `object` is a mathematical expression, such as `x`, `x + 1`, `R`,
  `{1, 2}`, `abs(x)`, or `fn(n N_pos) R`;
- a `fact` is a proposition about objects, such as `x > y`, `x $in R`,
  `1 + 2 = 3`, or `x = y or x < y or x > y`;
- a `statement` is a line or block that acts on the mathematical context, such
  as `have`, `forall`, `claim`, `thm`, `witness`, `by cases`, or `know`;
- a verification rule is a checker route for deciding whether a fact follows
  from the current context.

Each layer has builtin material.

A **builtin object** is an object form or name that Litex understands directly.
Not every builtin word is an object: `not`, `and`, `or`, `forall`, and `exist`
are builtin logical or factual forms because they express the shape of facts
and proofs. Builtin object heads are expressions such as standard sets,
arithmetic operations, tuple and set forms, or `abs(x)`. Some of these are
mainly for user convenience. The absolute value object `abs(x)` is a good
example: users could define a similar function themselves from basic order and
arithmetic, but the standard spelling is built in because ordinary mathematics
uses it constantly.

```litex
have fn self_abs(x R) R by cases:
    case x = 0: 0
    case x < 0: -x
    case x > 0: x
```

The point is not that `abs` is impossible to express without a builtin name.
The point is that writing `abs(x)` lets the verifier connect the expression to
the usual absolute-value rules without every file rebuilding that interface.

A **builtin fact** is trusted background already present when a user file
starts. Many of these are loaded as ordinary Litex statements inside the
builtin environment, such as operator typing facts, common comparison facts,
and standard relationships among familiar objects. For example, the usual
trichotomy of real numbers is available as background:

```litex
forall x, y R:
    x = y or x < y or x > y
```

This kind of fact is important because some ordinary mathematical axioms are
not single equalities. They may be disjunctions, implications, existence
facts, or universal facts. Litex needs those fact shapes to be first-class so
the background axiom can actually be used in later checking.

A **builtin statement** is a statement form that the executor understands as a
primitive context action. For example, `have` introduces objects, `forall`
checks universal facts, `claim` and `thm` prove reusable facts, `witness`
proves existential facts, and `by cases` organizes case proofs. These are not
ordinary mathematical objects. They are the proof-script actions that grow or
inspect the current context.

A **builtin verification rule** is different from a stored theorem. It is a
small verifier pattern that can close the current goal, often by looking at
equivalent forms or doing routine computation. For example, when the goal is
`x > y`, Litex can use common equivalent forms such as `y < x` or
`x - y > 0`:

Some of these routes are Rust-level verifier rules, while some common
equivalences are loaded as builtin `forall` facts in the initial environment.
The user-facing effect is similar: the verifier can use common mathematical
background without the current file proving a local lemma first.

```litex
forall x, y R:
    x - y > 0
    =>:
        x > y

forall x, y R:
    y < x
    =>:
        x > y
```

Builtin verification rules also cover calculation-style facts:

```litex
1 + 2 = 3
```

These rules matter because ordinary mathematical writing silently uses many
tiny equivalences and calculations. Without builtin rules, users would have to
write every bridge by hand: convert `x > y` to `y < x`, convert that to
`x - y > 0`, cite the arithmetic theorem for `1 + 2 = 3`, and so on. Litex
instead lets the user write the meaningful step while the verifier handles a
bounded amount of common background reasoning.

This convenience is also part of the trust boundary. Builtin objects, builtin
facts, builtin statement behavior, and builtin verification rules all deserve
tests, examples, and audit-friendly output. They are not hidden magic; they are
the built-in mathematical interface that makes short Litex proofs possible.

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

## Why not just import a big library and cite the theorem?

For many mature proof-assistant projects, importing a large library and citing
the strongest available theorem is the most efficient path. That is a real
advantage of systems with large libraries.

Litex is aimed at a different workflow, especially for textbooks and education.
If the goal is to formalize a calculus or analysis book, the proof script
should ideally show the derivation the book is teaching: definitions, local
lemmas, intermediate facts, and the way later results use earlier ones. If the
main work becomes "find a theorem in a mathematical dictionary and cite it",
the final result may verify, but the code no longer records the learning path.
It records where the result already exists.

Litex therefore tries to make the basic mathematical ground cheap enough that
users can write the book's proof directly. Builtin objects and small background
interfaces let the file get started without a huge import. Larger packages
still matter, but they should provide visible background or reusable interfaces,
not erase the central proof of the current chapter.

This is not a claim that imports are bad. It is a claim about where the
mathematical labor should live. For textbook-first formalization, the proof
script should be the derivation, not only a pointer into a theorem database.
In systems such as Lean or Isabelle, the large-library route is often excellent
formal engineering. Litex is exploring whether a lighter base can make the
book's own proof cheap enough to write and check directly.

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
prop facts. The verifier then asks whether the new fact follows from the
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
read `know P` as "assume P from this point onward." If a later `verification`
trace cites a fact that came from `know`, that trace explains why the later line
follows from the injected assumption; it does not show that the injected
assumption was proved by Litex.

Likewise, success on a `know` line only means the assumption was accepted into
the context. It is not a certificate that the injected fact was proved.

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
witness exist u R st {u > 0, u < 1} from 1 / 2:
    1 / 2 > 0
    1 / 2 < 1
have by exist v R st {v > 0, v < 1}: w
w > 0
```

The first block proves an existential fact. The `have by exist` line introduces
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
sketch:
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

This is also a textbook-design issue. When a file is following a book, imports
should not silently turn the chapter into theorem lookup. `stop import` gives
the author a way to keep a module available for explicit citation while making
the active proof context reflect the local derivation.

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
or short Manual examples rather than a separate prose page that can drift from
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
