# Lambda syntax, binding and reduction

## Purpose and source boundary

This pilot develops the ordinary untyped lambda calculus with de Bruijn
indices. Its conventional variable-binding treatment follows the nameless
representation described by N. G. de Bruijn,
[“Lambda calculus notation with nameless dummies” (1972)](https://www.sciencedirect.com/science/article/pii/1385725872900340).
The implementation and proofs are new source
constructions, not a claim to translate that paper or complete its
Church-Rosser development.

## Finite syntax as values

The raw encoders are natural-valued functions:

```text
variable_code(k) = 3*k
abstraction_code(b) = 3*b+1
pair_code(l,r) = (l+r)^2+l
application_code(l,r) = 3*pair_code(l,r)+2
```

These are encoding functions, not values denoting Litex function application.
The constructor tags are distinct. Pair row separation proves pair injectivity;
it also bounds each child by the pair code.

`is_lambda_closed(S)` describes subsets of N closed under those constructors.
`is_lambda_term(code)` means membership in every such closed subset. The actual
`Term` set is the least closed carrier. Its public constructors return Term,
and structural induction follows by applying the defining property to a
supplied constructor-closed subset of Term. A raw natural without this
membership cannot silently be used as a term.

This choice supplies real values and a genuine no-junk/structural-induction
principle. An assumed carrier with unproved constructor laws would hide the
central formalization obligation. A host function would instead denote a
semantic function and lose the object-language syntax being studied.

## Parsing and well-founded recursion

The three shape propositions describe an actual variable, abstraction or
application. Root-case and injectivity proofs give unique indices, bodies and
child pairs. The corresponding `have fn ... by exist!` declarations have exact
shape guards. A selector call on the wrong constructor stays ill-defined.

`syntax_rank(term)` is the term's natural encoding. Every abstraction body
and both application children have smaller rank, proved from the encoding
equations and pair bounds. Recursive shift/instantiation decrease this measure.
The explicit natural-valued rank keeps syntax values in Term while providing
the numeric measure consumed by the existing recursion checker.

## Avoiding capture

`shift(t,c,a)` is an actual Term-valued function. It leaves indices below c
alone, adds a to the rest, and uses c+1 under lambda. The zero-shift theorem
uses structural induction, with a set of terms satisfying the universal
cutoff property.

`instantiate(t,d,s)` removes a binder, rather than performing an unqualified
text replacement. At a variable k<d it preserves the variable. At k=d it
inserts `shift(s,0,d)`. At k>d it removes the vacated index by returning k-1.
Under lambda it recurses at d+1. Application recurses into both children.
These equations define the operation and preserve actual finite Term values.

The representative use contracts `(lambda x. lambda y. x) y`. The argument's
free index is raised across the remaining lambda, yielding lambda.Var1.
Constructor injectivity proves this differs from lambda.Var0. The general
equations also preserve inner bound variables and remove higher indices at
the deleted binder. A general free-variable/substitution metatheorem remains
a future theorem, not an additional assumption in these definitions.

## Beta reduction as a relation

`beta_contract(body,arg)` computes one root result. `is_root_beta_step` pairs
the corresponding redex with that result. `is_beta_step` intersects all
relations containing root contractions and closed under lambda, left
application and right application. It is the compatible one-step relation,
not a deterministic evaluator or its reflexive-transitive closure.

The introduction rules are proved from this definition. A closed relation
whose source must be a nonvariable proves that a variable cannot reduce.
The ordinary duplicator supplies Omega and its concrete beta self-step.
Confluence, a normalization strategy and decidability claims are not inferred
from those examples.

## Dependency map and remaining obligations

Signature/definition edges: native N and sets -> raw encoders -> least Term
carrier -> public constructors -> shape relations and unique parsing.
Proof/well-definedness edges: pair bounds and constructor equations -> strict
subterm rank -> recursive shift and instantiation -> zero shift, beta identity
and capture-sensitive results. Definition/proof edges: root contractions ->
compatible closure -> context rules, normal variables and the Omega step.

All of these implemented nodes have source proofs and use native mathematical
foundations. There is no new native Obj/Fact, trusted constructor assumption
or source axiom. Later typed calculi, richer metatheory and Lean compilation
remain separate work; their absence must not weaken the existing domains or
replace finite syntax with host functions.
