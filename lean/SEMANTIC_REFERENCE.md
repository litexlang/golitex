# Litex Lean semantic reference

This document audits the shared Lean target ABI used by Litex-to-Lean. It
answers four questions for every declaration currently exposed by
[`Litex.Core`](Litex/Core.lean) and every theorem currently proved in
[`Litex.Rules`](Litex/Rules.lean):

1. What source-level Litex concept does it represent?
2. Where is the underlying mathematical concept developed in Terence Tao's
   *Analysis I*?
3. Why is it an `axiom`, `def`, `structure`, `instance`, or `theorem` in Lean?
4. Is it a settled semantic boundary, a target representation device, an
   extension beyond the book, or known implementation drift?

The reference covers ABI version 10. The number of declarations is not a
measure of foundational minimality: several declarations are fields of one
intended model that have not yet been consolidated or constructed.

## Source and citation policy

The numbered book references below use Terence Tao, *Analysis I*, third
edition, Springer, 2016. The official
[Springer record](https://link.springer.com/book/10.1007/978-981-10-1789-6)
lists the relevant progression: natural numbers in Chapter 2, set theory and
functions in Chapter 3, integers and rationals in Chapter 4, real numbers in
Chapter 5, and infinite products and choice in Chapter 8.

Tao deliberately presents enough foundations for analysis without fixing one
fully formal metatheory. On his official
[*Analysis I* page](https://terrytao.wordpress.com/books/analysis-i/), he
explains that primitive mathematical objects may be treated axiomatically and
that the text leaves room to add new kinds of objects. This ABI makes one more
specific choice than the book: it selects the pure-set option described in
Remark 3.1.3, while retaining numbers, functions, and sets as distinct public
mathematical interfaces.

The correspondence labels used below have precise meanings:

- **Direct concept:** the Lean declaration represents the named book concept,
  although its target encoding may differ.
- **Pure-set specialization:** the book explicitly permits both pure and
  impure readings; Litex selects the pure reading.
- **Representation bridge:** the declaration connects Litex objects to
  Mathlib values or explicit target proof evidence. It is not asserted by the
  book.
- **Extension:** the concept is useful to Litex but is not developed in
  *Analysis I*.
- **Engineering:** the declaration versions or packages the compiler ABI and
  has no mathematical source claim.
- **Current drift:** the declaration is a known temporary mismatch between the
  decided source semantics and ABI version 10.

These labels prevent a citation from doing more work than it really does.
*Analysis I* motivates the mathematical interfaces; it does not prove that
this particular Lean ABI is a model of Litex.

## What the Lean declaration kinds mean

| Lean form | Role in this package | Additional trusted mathematics? |
| --- | --- | --- |
| `axiom` in `Litex.Core` | A primitive interpretation boundary for source objects, membership, numeric representation, arithmetic, or functions. | Yes. Lean checks uses of the declaration but does not prove the declaration itself. |
| `def` | A transparent abbreviation or proposition built from earlier declarations. | No. Its body can be unfolded by Lean. |
| `structure` | Transparent data needed by the target ABI. | No additional proposition is assumed. |
| `instance` | Lean notation or elaboration support for an existing operation. | No additional proposition is assumed. |
| `theorem` in `Litex.Rules` | A concrete verifier rule proved once from `Litex.Core` and Mathlib. | No new axiom; Lean kernel-checks the proof. |
| generated `axiom` for a source `trust` | The exact proposition explicitly trusted by Litex source. | Yes, but it is source-local and is not silently added to this shared core. |

This is why the implementation file is named `Core.lean`, not `Axioms.lean`:
the module contains axioms, transparent definitions, a structure, notation
instances, and the contracts from which ordinary theorems are proved.

## Tracer: proof-free addition with local WD evidence

The central example is:

```lean
axiom add : Object → Object → Object
```

Addition itself occurs throughout the book: Definition 2.2.1 introduces
natural-number addition; Definition 4.1.2 defines integer addition;
Definition 4.2.2 defines rational addition; and Definition 5.3.4 defines real
addition on Cauchy representatives. The shared target operation uses `C` as
Litex's largest current numeric domain. That choice of a complex super-domain
is an extension beyond *Analysis I*, not a theorem quoted from it.

The target term is independent of the proof route used to establish Litex
well-definedness. Litex still rejects `a + b` until it has proved the exact
facts `In a C` and `In b C`; generated Lean replays those facts as local
`have` steps in the proof environment that owns the expression. The frozen
arithmetic object recipe also records `C` as its intrinsic result carrier, so
an outer expression such as `(a + b) + c` gets a local result-membership step
after `intro`; this result evidence never becomes a constructor argument or a
top-level generalized fact. The
representation law

```lean
add_embedComplex
```

says that, on represented complex values, the source operation agrees with
Mathlib addition. Then `complexAddClosure` and `realAddClosure` are proved in
`Litex.Rules`; they are not additional axioms. Thus the path is:

```text
book arithmetic concept
  -> Litex operation plus source well-definedness
  -> one shared representation axiom
  -> kernel-checked closure theorems
  -> generated proof citing the verifier's exact membership facts
```

This tracer does not show that every Litex arithmetic rule has been ported.
ABI version 10 treats `div a b` the same way: its object denotation is total at
the representation layer, while both complex memberships and the exact
denominator-nonzero fact remain mandatory source certificates and local Lean
proof steps. Power, transcendental operations, and many arithmetic
certificates remain outside the current target coverage.

## `Litex.Core` declaration ledger

### Version, objects, and sets

| Declaration | Lean form | Analysis I anchor | Exact role and boundary |
| --- | --- | --- | --- |
| `abiVersion` | `def` | None; engineering. | Records the shared ABI revision for coordinated version review. Generated files do not mention it. |
| `Object` | `axiom` | Remark 2.1.14 (objects are treated by their properties), Axiom 3.1 (sets are objects), and Remark 3.1.3 (pure set theory). | The meta-level carrier of all source Litex objects. `Object : Type` is not itself a term of type `Object`, so it is not an internal universal set. |
| `In` | `axiom` | Definition 3.1.1 (elementhood). | Interprets source `$in` as a relation between two represented objects. Membership is evidence, not Lean typing or a cast. |
| `IsSet` | `def` | Remark 3.1.3, specialized to its pure branch. | Definitionally `True`, exactly recording the decided Litex semantics that every well-defined source object is set-like without adding a classifier axiom. |
| `everyObjectIsSet` | `theorem` | Remark 3.1.3, pure-set specialization. | Compatibility theorem proved from the definitionally true `IsSet`; it adds no trust. |
| `IsNonemptySet` | `def` | Axiom 3.2 and Lemma 3.1.6 (a nonempty set has an element). | Defines nonemptiness exactly by an `In` witness; no redundant sethood conjunct remains in the pure model. |
| `IsFiniteSet` | `def` | Definition 3.6.10 (finite cardinality). | Views the `In`-extension of one object as a Mathlib set and asks it to be finite. Tao defines finite cardinality using a bijection with a finite standard set, so this is a target representation of the same intended notion, not a derivation of their equivalence inside the current core. |

### Total objects, set builders, ranges, and aggregate families

| Declaration | Lean form | Analysis I anchor | Exact role and boundary |
| --- | --- | --- | --- |
| `pi` | `def` | No direct anchor in *Analysis I*; representation bridge. | Represents source `pi` by Mathlib's real pi inside `embedComplex`; construction is total. |
| `union` | `axiom` | Section 3.4 (unions). | Total binary source union object. Its sethood and membership laws remain separate proof interfaces. |
| `intersect`, `setMinus` | `axiom`s | Section 3.4 and ordinary set difference. | Proof-free binary set denotations, characterized by conjunction and negated membership at the `In` boundary. |
| `bigUnion`, `bigIntersect` | `axiom`s | Section 3.4 (unions and intersections of families). | Proof-free family operations with existential/universal membership characterizations over represented objects. |
| `powerSet` | `axiom` | Axiom 3.4 (power set). | Proof-free power-set denotation; membership is exactly the represented `Subset` relation. |
| `setBuilder`, `inSetBuilder_iff` | `axiom`s | Axiom 3.5 (specification). | Packages a base object and predicate, and gives the exact conjunction used to replay checked membership. The predicate binder is target-local and owned by its source `SymbolId`. |
| `IsTuple` | `axiom` | Finite ordered families; target extension. | Records the source tuple predicate for one representative indexed aggregate recipe. |
| `range`, `closedRange`, `inRange_iff`, `inClosedRange_iff` | `axiom`s | Finite integer intervals; target extension. | Represent half-open and closed integer ranges without identifying them with native Lean finite types; their laws retain integer membership and exact lower/upper bounds. |
| `tupleDim`, `atIndex` | `axiom`s | Finite sequence dimension and coordinate notation; target extension. | Expose the two source projections as object-valued operations. |
| `tupleObject` | `axiom` | Finite ordered families; target extension. | Proof-free denotation of a dimensioned tuple family. Positive-dimension and lower-bound checks remain verifier-owned proof evidence. |
| `tupleObjectIsTuple`, `tupleObject_dim`, `tupleObject_at` | `axiom`s | Same indexed-family concept; representation bridge. | Export the exact three stored effects of `HaveTupleStmt`; they do not generalize matrices, sequences, or arbitrary aggregates. |
| `tupleLiteral`, `sequenceLiteral`, literal dimension laws | `axiom`s | Finite ordered families; target extension. | Preserve the distinction between tuple and sequence literal syntax while exposing their source length as an object-valued dimension. |
| `finiteSequenceSet`, `sequenceSet` | `def`s | Function spaces indexed by finite positive integer intervals or positive naturals. | Reuse the ordinary `fnSpace1` ABI instead of introducing a second sequence carrier model. |
| `generalCart`, `inGeneralCart_iff` | `axiom`s | Axiom 3.10 and Chapter 8's product/choice interface. | A member is both a function from the index set into the union of the family and a pointwise choice function. This does not prove the axiom of choice. |
| `finiteSetSum`, `finiteSetProduct`, `finiteSetReduce` | `axiom`s | Finite iteration; target extension. | Proof-free fold denotations. Finiteness, callable ranges, seeds, and associative/commutative laws stay in verifier-owned WD evidence. |
| `sum`, `product`, `reduce` | `def`s | Finite iteration over closed integer intervals; target extension. | Transparent aliases for the corresponding finite-set fold over `closedRange start finish`, matching the verifier's index carrier. |

### Numeric objects and refinements

The book constructs successive number systems. The ABI instead represents
their already-accepted Litex interfaces inside one object universe. It does
not replay the book's quotient and Cauchy constructions every time a numeral
appears in generated Lean.

| Declaration | Lean form | Analysis I anchor | Exact role and boundary |
| --- | --- | --- | --- |
| `N` | `axiom` | Definition 2.1.1 and Axioms 2.1--2.5. | The Litex natural-number set as an object. |
| `Z` | `axiom` | Definition 4.1.1. | The Litex integer set as an object; the book's formal-difference construction supplies its mathematical meaning. |
| `Q` | `axiom` | Definition 4.2.1. | The Litex rational set as an object; the book's formal-quotient construction supplies its mathematical meaning. |
| `R` | `axiom` | Definition 5.3.1. | The Litex real set as an object; the book constructs reals from rational Cauchy sequences. |
| `C` | `axiom` | No direct anchor in *Analysis I*; extension. | Litex's complex-number set and the current common arithmetic domain. It must not be presented as a concept established by this book. |
| `NPos` | `axiom` | Definition 2.2.7. | Target object for Litex `N+`, the positive natural numbers. |
| `ZNeg` | `axiom` | Lemma 4.1.5 and Definition 4.1.10. | Target object for Litex `Z-`, the negative integers. |
| `ZStar` | `axiom` | Definition 4.2.1 uses nonzero integer denominators; Proposition 4.1.8 supplies the relevant nonzero algebra. | Target object for Litex `Z*`, the nonzero integers. The book does not introduce this exact carrier name as a separate foundational set. |
| `QPos`, `QNeg` | `axiom`s | Definition 4.2.6. | Target objects for positive and negative rationals. |
| `QStar` | `axiom` | Proposition 4.2.4 and Remark 4.2.5. | Target object for nonzero rationals, the reciprocal domain. |
| `RPos`, `RNeg` | `axiom`s | Definition 5.4.3. | Target objects for positive and negative reals. |
| `RStar` | `axiom` | Definition 5.3.16. | Target object for nonzero reals, the reciprocal domain. |
| `CStar` | `axiom` | No direct anchor in *Analysis I*; extension. | Target object for nonzero complex values. |

The comparison interface consists of `Lt` and `Le`, with `lt_embedReal` and
`le_embedReal` as representation laws for embedded Mathlib reals.
`inNPos_iff` and `inRPos_iff` supply the witnesses used by the checked
positive-natural reflection and `positiveRealMembership` theorems, while
`isSetR` is a theorem of the definitionally true sethood predicate. These are representation
bridges for source order and carrier predicates, not a claim that all ordered
number-system laws have been ported.

ABI version 10 declares the refined numeric objects but does not yet include
their full membership-characterization laws. They should therefore be read as
opaque ABI placeholders whose intended source meanings are listed above, not
as a completed Lean development of every refined carrier.

### Native numeric representation

| Declaration | Lean form | Analysis I anchor | Exact role and boundary |
| --- | --- | --- | --- |
| `embedComplex` | `axiom` | None; representation bridge. | Embeds Mathlib complex values into the universal object carrier so one Arabic numeral denotes one target object. |
| `embedComplex_injective` | `axiom` | Abstract equality is discussed in Remark 2.1.14 and Appendix A.7, but this exact statement is a representation bridge. | Prevents distinct native complex values from collapsing to one represented object. |
| `inN_iff` | `axiom` | Chapter 2's natural-number system. | Characterizes `In x N` by a native `Nat` witness embedded through `embedComplex`. |
| `inZ_iff` | `axiom` | Definition 4.1.1. | Characterizes `In x Z` by a native `Int` witness. This realizes the accepted integer interface rather than reproducing formal differences in the ABI. |
| `inQ_iff` | `axiom` | Definition 4.2.1. | Characterizes `In x Q` by a native rational witness. |
| `inR_iff` | `axiom` | Definition 5.3.1. | Characterizes `In x R` by a native real witness. |
| `inC_iff` | `axiom` | No direct *Analysis I* anchor; extension and representation bridge. | Characterizes `C` as exactly the represented Mathlib complex values. |
| `OfNat Object` | `instance` | Definition 2.1.3 introduces the numerals from zero and successor. | Makes Lean numerals elaborate to `embedComplex (n : Complex)`. It introduces notation, not a new proposition. |

The five `in..._iff` axioms identify the ordinary inclusions
`N -> Z -> Q -> R -> C` at the level of one object: a numeral is not copied or
cast to a new `Object` when another membership fact is proved.

### Arithmetic operations and coherence

| Declaration | Lean form | Analysis I anchor | Exact role and boundary |
| --- | --- | --- | --- |
| `add` | `axiom` | Definitions 2.2.1, 4.1.2, 4.2.2, and 5.3.4. | Proof-free represented addition. The source certificate still records two ordered `In _ C` obligations, replayed locally; the choice of `C` is a Litex extension. |
| `sub` | `axiom` | Definition 4.1.4 introduces negation; subtraction is obtained from addition and negation throughout Chapters 4 and 5. | Proof-free represented subtraction with the same source WD contract as `add`. |
| `mul` | `axiom` | Definitions 2.3.1, 4.1.2, 4.2.2, and 5.3.9. | Proof-free represented multiplication whose complex-membership obligations remain verifier evidence. |
| `div` | `axiom` | Rational division and field structure in Section 4.2; real reciprocals in Definition 5.3.16. | Proof-free represented division. The two `In _ C` obligations and denominator-nonzero obligation remain mandatory source certificates and local proof steps. |
| `add_embedComplex` | `axiom` | Arithmetic concepts above; exact equation is a representation bridge. | Makes represented addition agree with Mathlib complex addition. |
| `sub_embedComplex` | `axiom` | Arithmetic concepts above; exact equation is a representation bridge. | Makes represented subtraction agree with Mathlib complex subtraction. |
| `mul_embedComplex` | `axiom` | Arithmetic concepts above; exact equation is a representation bridge. | Makes represented multiplication agree with Mathlib complex multiplication. |
| `div_embedComplex` | `axiom` | Sections 4.2 and 5.3; the exact equation is a representation bridge. | Makes represented division agree with Mathlib complex division. Source acceptance and generated closure proofs separately retain the membership and nonzero obligations. |

The coherence declarations are axioms because `Object` and its operations are
currently abstract. A later concrete model could turn some or all of them into
definitions and proofs without changing their public mathematical contract.

### Proof-free finite set literals with checked pairwise WD

| Declaration | Lean form | Analysis I anchor | Exact role and boundary |
| --- | --- | --- | --- |
| `ListSetWellDefined` | `def` | Axiom 3.2 (pair set) and finite extensional set notation; the ordered no-duplicate certificate is Litex-specific engineering. | Defines the exact source WD invariant as `List.Pairwise (· ≠ ·)`. It lives in `Prop`, so the selected proof route does not become mathematical object data. |
| `listSet` | `axiom` | Axiom 3.2 and finite unions built in Section 3.4. | Proof-free represented finite-set denotation. Litex's complete indexed pairwise-distinctness matrix remains a mandatory checked certificate and local proof trace. |
| `inListSet_iff` | `axiom` | Extensional membership meaning of finite set notation. | States that membership in the represented list set is exactly list membership. |

### Functions, function spaces, and choice functions

| Declaration | Lean form | Analysis I anchor | Exact role and boundary |
| --- | --- | --- | --- |
| `arg` | `def` | None; compiler machinery. | Reads a zero-based argument from the target list. Its default value is irrelevant only when the emitted arity proof guarantees the requested position exists. |
| `FnSpec` with `arity`, `requirements`, and proof-dependent `range` | `structure` | Definition 3.3.1 (vertical-line/function contract). | Packages one exact Litex application layer. `range args hLength hRequirements` may consume the same ordered WD evidence as the body, so a partial source range is never totalized merely to fit Lean. The list and proof telescope are target machinery, not Tao's definition. |
| `FnSet` | `axiom` | Axiom 3.10, the set `Y^X` of functions from `X` to `Y`. | Turns a target function specification into a source-level function-space object. |
| `Applicable` | `axiom` | Definition 3.3.1 requires an input to be in the function's domain; exact proposition is a representation bridge. | Records that one function object can be applied to one exact argument list. |
| `apply` | `axiom` | Definition 3.3.1 and the notation `f(x)`. | Proof-free application denotation. `Applicable` remains a separate proposition replayed for every exact source layer. |
| `IsChoiceFunctionFor` | `def` | Definition 8.4.1 (infinite products as choice functions) and Axiom 8.1 (choice). | Defines the pointwise condition that a chooser selects a member of each family value. The retained `_familySet` argument preserves the source predicate's public arity; its carrier obligations are checked by Litex well-definedness rather than repeated in this proposition. This definition is not itself the axiom of choice. |
| `CoeFun Object` | `instance` | Function-application notation in Section 3.3. | Lets Lean print and elaborate `f args` using `apply`; it is syntax support, not an assertion that every object is callable. |
| `fnSetApplicable` | `axiom` | Definition 3.3.1 and Axiom 3.10. | From exact function-space membership, arity, and requirements, constructs the separate applicability certificate for the source application layer. |
| `fnSetResult` | `axiom` | Definition 3.3.1: a function sends each domain input to its declared codomain. | Proves that a certified application belongs to `range args hLength hRequirements`, preserving the exact arity and requirements evidence. |
| `functionObject` | `axiom` | Definition 3.3.1. | Proof-free function-object denotation from its exact `FnSpec` and dependent body; the selected closure proof is not object data. |
| `functionObjectInFnSet` | `axiom` | Axiom 3.10. | Consumes the verifier-owned pointwise closure proof to establish the proof-free function object's exact function-space membership. |
| `functionObjectApplicableLength` | `axiom` | Definition 3.3.1; representation bridge. | Recovers the exact arity certificate from an already named `Applicable` proof so definition reduction can call the proof-dependent body. |
| `functionObjectApplicableRequirements` | `axiom` | Definition 3.3.1; representation bridge. | Recovers the exact ordered requirements certificate from an already named `Applicable` proof. |
| `functionObject_apply` | `axiom` | Definition 3.3.1 and function evaluation. | Uses the exact stored defining equality through the two applicability projections; unavailable defining `FactId`s remain compiler errors. |

`IsChoiceFunctionFor` should not be confused with a proof of Axiom 8.1. It
only defines what a displayed chooser must satisfy. A source use of the axiom
of choice remains explicit trust unless its particular instance is proved by
other means and compiled through a supported proof route.

## `Litex.Rules` theorem ledger

Every declaration in this section is a Lean `theorem`, not an axiom. The
theorems expose concrete verifier rules while keeping their proof dependencies
inside the shared library.

| Theorem | Analysis I anchor | What Lean actually checks |
| --- | --- | --- |
| `notEqualSymmetry` | Appendix A.7, symmetry of equality and inequality. | Applies Lean's proved symmetry rule for `!=`. |
| `numeralInN` | Definition 2.1.3 and the Chapter 2 natural-number axioms. | Builds the `inN_iff` witness for a native `Nat`. |
| `numeralInNPos` | Definition 2.2.7. | Builds the `inNPos_iff` witness from an explicit native positivity proof. |
| `numeralInZ` | Definition 4.1.1 and the embedding `n` as the formal difference `n--0`. | Builds the `inZ_iff` witness for the same numeral object. |
| `numeralInQ` | Definition 4.2.1 and the embedding of an integer as `a//1`. | Builds the `inQ_iff` witness for the same numeral object. |
| `numeralInR` | Definition 5.3.1 and the constant rational Cauchy-sequence embedding. | Builds the `inR_iff` witness for the same numeral object. |
| `numeralInC` | No direct *Analysis I* anchor; extension. | Builds the `inC_iff` witness for the same numeral object. |
| `negativeNumeralInC` | No direct *Analysis I* anchor; complex extension. | Represents a negative source integer by the proof-free object `0 - n` and derives its complex membership from `complexSubClosure`. |
| `realSetNonempty` | Axiom 3.2 and the existence of zero in the real-number system. | Uses the checked numeral-real membership theorem to produce the direct witness for `IsNonemptySet R`. |
| `objectIsSet` | Remark 3.1.3, pure-set specialization. | Re-exports `everyObjectIsSet`; both theorems follow from the definitionally true `IsSet` and add no semantic axiom. |
| `numeralLt` | Chapter 2 numeral order and Section 5.4 real order. | Reduces a closed natural-literal `Litex.Lt` proposition to native natural order through the real embedding. |
| `numeralLe` | Chapter 2 numeral order and Section 5.4 real order. | Reduces a closed natural-literal `Litex.Le` proposition to native natural order through the real embedding. |
| `positiveRealMembership` | Definition 5.4.3. | Opens the retained `RPos` representation witness and proves the source `Litex.Lt 0 x` fact through `lt_embedReal`. |
| `naturalInInteger` | Definition 4.1.1, using `n--0`. | Converts an `N` membership proof into a `Z` membership proof without changing the object. |
| `integerInRational` | Definition 4.2.1, using `a//1`. | Converts `Z` membership into `Q` membership without changing the object. |
| `rationalInReal` | Definition 5.3.1, using a constant rational Cauchy sequence. | Converts `Q` membership into `R` membership without changing the object. |
| `realInComplex` | No direct *Analysis I* anchor; extension. | Converts `R` membership into `C` membership through Mathlib's real-to-complex embedding. |
| `complexAddClosure` | Complex extension; addition pattern parallels the book's number-system closure laws. | Opens both `C` witnesses, uses `add_embedComplex`, and constructs a `C` witness for the result. |
| `complexSubClosure` | Complex extension. | Proves represented complex subtraction is closed. |
| `complexMulClosure` | Complex extension. | Proves represented complex multiplication is closed. |
| `complexDivClosure` | Complex extension. | Uses the retained two complex-membership proofs and denominator-nonzero proof to form the represented quotient and prove it remains in `C`. |
| `integerAddClosure` | Definition 4.1.2. | Opens the retained integer witnesses, uses represented addition coherence, and proves the result remains in `Z`. |
| `integerSubClosure` | Definition 4.1.4. | Proves represented subtraction preserves integer membership. |
| `integerMulClosure` | Definition 4.1.2. | Proves represented multiplication preserves integer membership. |
| `realAddClosure` | Definition 5.3.4 and Proposition 5.3.11. | Uses retained `C` facts to form the term and retained `R` facts to prove the result is real. |
| `realSubClosure` | Section 5.3 real algebra. | Proves represented subtraction preserves real membership. |
| `realMulClosure` | Definition 5.3.9 and Proposition 5.3.11. | Proves represented multiplication preserves real membership. |
| `realDivClosure` | Definition 5.3.16 and real field arithmetic. | Consumes the exact complex memberships and denominator-nonzero proof used to construct the quotient, then uses the retained real memberships to prove the result is real. |

The hierarchy theorems are important evidence for the universal-object model.
For example, `rationalInReal` produces another proposition about the same
`x : Object`; it does not convert a value of Lean type `Rational` into a new
value of Lean type `Real`.

## What is and is not established

This ledger establishes an auditable design correspondence:

- each shared declaration has a stated role;
- every claimed *Analysis I* connection names a chapter item;
- target-only machinery and complex-number extensions are labelled as such;
- ordinary builtin rules are distinguished from unproved semantic axioms;
- known ABI drift is visible rather than silently rationalized.

It does **not** establish that the current axioms are independent, minimal, or
jointly consistent. It also does not establish a full model of ZF or ZFC,
nor that every Litex verification route can already be emitted and accepted by
Lean. Those stronger claims require a concrete model or relative-consistency
argument, a completed compiler coverage audit, and real Lean compilation gates
for every supported route. The narrower compiler requirement is described in
the [universal object design](../src/compile_to_lean/litex_object_design.md).

In particular, "inspired by *Analysis I*" is not used as a substitute for a
soundness argument. The book supplies the mathematical development and named
concepts. Litex chooses a source semantics. `Litex.Core` states the current
target interpretation boundary. `Litex.Rules` proves reusable
consequences. Generated Lean must then replay the exact verifier evidence
without inventing memberships, applicability certificates, or target-side
proof search.

## Maintenance rule

Any change to this ABI should update this reference in the same change:

1. list every new or changed declaration by exact Lean name;
2. classify it as direct concept, pure-set specialization, representation
   bridge, extension, engineering, or current drift;
3. give an exact *Analysis I* item when a book correspondence is claimed, or
   explicitly state that there is no direct anchor;
4. justify why an unproved proposition belongs in `Litex.Core` instead of
   being a theorem in `Litex.Rules`;
5. update or remove the relevant drift note;
6. review `abiVersion` whenever generated files compiled against the previous
   signature would no longer typecheck or would acquire different semantics.
