# A higher-order logical world in Litex

## Purpose and source

The source is the existing attributed `examples/hol_embedding.lit` development
provided by chegnxuan huang. This showcase preserves its mathematical declarations
and proof order, with a local caller demonstrating the checked interpretation.
Its scope does not include reconstruction of the HOL Light kernel.

## Boolean values and logical assertions

False is the empty set and True is its singleton. `Bool` is their two-element
carrier. Their distinctness is proved. `holds(b)` means b=True; it is a
proposition about a Boolean value, not another Boolean-valued operation.

The connectives and quantified operators are actual functions into Bool.
A predicate on A is an ordinary complete function A->Bool, so it can be
passed as a value or used in a higher quantifier's domain. `all_true` and
`some_true` describe their meanings, and the introduction/elimination
theorems connect those meanings to `holds`.

An uninterpreted logical predicate would not supply a Boolean value for a
larger expression. Conversely, merely declaring a Boolean-valued function
does not prove that it holds. The separate interfaces retain this distinction.

## Functions, choice and infinity

Beta uses host function application; eta/extensionality use host function
equality on the same complete domains. These are shallow semantic laws.
They do not define a separate term language with object-level substitution.

The Hilbert choice construction uses inhabited candidate sets: satisfying
elements if any exist, otherwise the entire nonempty carrier. Native choice
supplies a function choosing from those candidates. The select theorem only
promises satisfaction when a satisfying element exists; an impossible
predicate receives no satisfying-witness guarantee.

Native N and successor interpret the infinity axiom. Eta/select axiom
interpretations retain their specified nonempty type parameters. None of
these source theorems remove the host's mathematical foundation.

## Constructed naturals and arithmetic

The constructed representative carrier is the intersection of all predicates
containing the chosen zero and closed under the chosen successor. `HolNat`
uses that actual carrier. The source proves zero/successor laws, induction
and cases before defining numeral conversion and addition by iteration.
Unique numeral indices justify the inverse conversion.

The arithmetic results concern this constructed carrier and its operations,
with an explicit relationship to host N. The native N dependency is visible;
this is not a construction of all arithmetic without any ambient infinite set.

## Dependencies and boundaries

Definition/signature edges: host sets/functions -> Boolean carrier -> holds,
connectives, equality and quantifiers. Proof/existence edges: native choice and
nonempty candidates -> Hilbert selection -> interpreted select axiom; native
N/successor -> interpreted infinity -> least successor-closed carrier ->
induction and unique numeral indices -> addition and examples.

The import extraction preserves those declarations and proofs without new
axioms or source trust. The standalone example is a provenance source, not a
runtime import dependency. A future deep HOL embedding must separately define
syntax, typing, substitution and derivations and prove their semantic rules;
the current module does not imply that work has been done.
