# Interactive textbook reading

**The source is the textbook and the primary reading interface.** Definitions,
mathematical statements and proofs are expressed in Litex source, with inferred
facts displayed beside the statements that produce them. Definitions, parameter
domains and proof references are accessible by interacting with that source.
Readers do not need to open a separate Info View to follow the mathematics.
Explanations and proof grounds open on demand beside the selected source.
There is no standing mathematical-meaning pane; readers close the contextual
explanation to return to the unobstructed source.

Repeated local claims keep the proof of the selected execution. For example,
a function introduced with `have fn ... by exist!` can follow its saved unique
existence premise to the corresponding local `claim`, then to that execution's
witness. An atomic claim can similarly follow its closing `by def` or `by thm`
step. Source hover, pinning, later reuse, inference origins and Back preserve
the actual execution even when the native source FactId is shared. The source,
returned goal, successful closing proof, retained local scope and proof-body
statement references must agree; missing correspondence is shown as incomplete.
The original fact owner and default `selectFact(id)` address stay unchanged.
Atomic and supported compound claim goals keep their retained formation
checks closed at the end of the proof explanation. Universal, existential,
unique-existence, negated-universal, conjunction, disjunction and chain goals
use the actual certificates and checking scope. A failed proof may retain
successful formation checks; those checks do not prove or publish the goal.
Unsupported `claim` equivalence goals are identified as a command boundary,
not as false statements. Missing or conflicting records remain incomplete.
This does not certify distinct generated function-check scopes that share one
statement/fact/source address or every cached/result variant.

Ordinary `exist`, `exist!` and `not exist` verification also keeps its retained
candidate-expression checks closed at the end. The checking scope belongs to
that execution; candidate parameters and assumed body conditions supply no
chosen witness, uniqueness or nonexistence proof. A failed proof search can
retain successful formation checks without publishing a conclusion. Builtin,
stored-existence and universal-instantiation proofs keep their own grounds.
Object introductions and counterexamples display a shared certificate once at
their enclosing explanation's end. Missing or conflicting correspondence is
reported as incomplete, and source edits invalidate the old explanations.

Source rows with existing proof, logical-action or failure explanations also
have a small `▸` immediately after their source text. For example,
`p(1) + p(2) = 3  ▸` opens the same retained proof as the row hover and keeps
it open after the pointer leaves. Clicking again, Escape, the close control
or an outside click closes it; opening another row replaces it. The native
button exposes its expanded state and supports keyboard focus. An ordinary
click also works through the editor's input surface without moving the caret
or adding source rows. Editing removes stale buttons and explanations.
Existing hover previews remain available. The button uses the shared source
preview and its exact citation/Back addresses; it adds no proof records and
does not invent an explanation for source-only rows.

Documented lexical names such as `sqrt` and the complete `by contra` phrase
also have an adjacent raised `▸`. Its native button occupies no source advance:
the original token, following punctuation and editor text keep their positions.
It opens the exact existing operation/statement help and shares persistent
display, dismissal and focus with the sentence button. Help does not establish
the containing statement, and an invalid application keeps its rejected status.
Each occurrence owns its button; ordinary resolved variables, punctuation and
numeric literals keep their original controls. Hover remains available, while
an explicitly opened explanation suppresses competing transient tooltips.

The editable native-preview acceptance uses an actual `.lit` file with
`-reading -f`. The selected `-e` preview renders the same input, but its
recheck request currently retains a `<eval>` dependency filename that the
upload boundary rejects. This existing inline-source recheck limitation is
separate from the sentence button; the file-based recheck path is verified.

## Mathematical language help

`language_reference.json` owns bilingual semantic descriptions of statement
forms and selected mathematical operations. Shared keyword spellings refer to
the statement owner rather than duplicating its prose. The offline generator
embeds this data in the existing shared reader; no extra network request,
runtime service or standing information pane is required.

Equivalent infix spellings may reference one canonical entry in this source
catalogue, with only syntax and lexical role overridden. The generator rejects
missing targets and reference chains, then emits ordinary complete cards; the
browser keeps no second reference resolver. In particular, `∪`, `∩`, `×` and
`∘` share the mathematical descriptions of their named operations. Native
tokenizer aliases such as `ℝ+`, `∀`, `∈` and `∃!` retain canonical-token help.

Postfix `!` shares the factorial description; it is distinct from the complete
`exist!` keyword. Structure prefixes, field dots, template backslashes and the
closed-integer-range `...` spelling also retain their semantic cards without
expression-position metadata. Exact expression hints and resolved declaration
identities continue to take precedence. These fallback cards describe the
spelling, not a newly established fact or a guessed field declaration.

```sh
python3 src/reading/generate_language_reference.py --check
python3 src/reading/generate_highlighting.py --check
python3 src/reading/audit_language_reference.py --output <task-owned-report.json>
```

The audit inventories current AST dispatcher branches separately from parser
spellings. An explanation card, a short label, a removed spelling, a
context-dependent user definition and an unresolved surface are distinct
states. A catalogue entry is not proof of correct hover anchoring or coverage
of the associated verification result. The report deliberately retains missing
and unresolved entries; it must not be used to claim all proof forms are covered.
Nested property-kind fields are not separate AST-branch counts, and the three
identifier encodings share one identifier form.

Builtin theorem identities have a separate audit denominator. A resolved
theorem category or successful application is not counted as an authored
mathematical description of that theorem. The report distinguishes specific
name-hover explanations, generic labels and available bilingual catalogue
comments; AST `Identifier` coverage cannot substitute for this check.

`builtin_theorems` is an optional source-catalogue table keyed by the native
`BuiltinTheoremId` variant. The generator validates canonical names and arities
against the live native dispatch and embeds plain bilingual cards with native
canonical names and declared arities. The reader selects these from retained
builtin callee/application identities or the source observer's optional
`symbols[].builtin_theorem` declaration identity. The latter is produced only
for typed bare theorem calls resolved by `BuiltinTheoremId::from_name`; it
contains `type`, canonical `name` and declared `arity`, while the symbol kind
is `builtin_theorem`. It remains available on rejected calls and does not
record a proof, rule application or successful invocation. Qualified and user
theorem names do not receive this native identity. Conflicting declaration and
application identities fail closed, with matching rule identity when present.
A theorem spelling, user declaration or
unknown/malformed native identity cannot supply a borrowed description. Older
exports with a retained successful typed identity do not require catalogue
messages or the new optional declaration metadata.

These cards state the mathematical law, domains, obligations and a checked
source example; they do not manufacture premise proofs or parameter bindings.
The ordinary theorem-application view continues to show the actual call's
requirements, stored conclusions and final collapsed WD independently. Kernel
catalogue comments are audited separately from these viewer-owned descriptions.

Membership descriptions retain complete function/tuple domains, every
comprehension condition, and the set-valued condition in family-intersection
projections. Real-bound descriptions distinguish a supplied bound, a proposed
extremum, and an existentially obtained certified extremum; they preserve the
strict comparisons needed for crossing and rational-density conclusions.

Sequence-limit descriptions retain positive-integer domains, the complete
epsilon/cutoff quantifier order, and both nonzero premises for a full-domain
quotient. Finite limsup/liminf descriptions distinguish eventual bounds from
hits on every tail; negation and negative scaling exchange the two kinds.
Candidate proofs, existence propositions and proof-consuming selectors remain
separate, and sum-bound cards state the interface's explicit absolute bounds.

Leading keywords use the actual captured statement kind: `have` for an arbitrary
element differs from `have` for an equality definition, and a function defined by
cases differs from one given by a single body. The longest documented phrase is
recognized over adjacent tokenizer spans, including three-word commands such as
`release tuple def`. Phrases cannot cross comments, newlines or resolved symbol
occurrences. Clicking and hovering use the same statement-specific card, while
the public keyword-selection identity remains the authored syntax spelling.
Mapped equality operators retain their own proof selection. Resolved builtin
set identities receive full number-set descriptions; user symbols keep their
own declarations. Missing statement kinds fall back to language-level help.

Object-operation cards describe the actual parameter order, domains and result
meaning. Integer `range` is half-open while `sum` and `product` include both
endpoints; ordered folds differ from commutative finite-set folds; complex inner
products conjugate the first argument while outer products do not. Matrix
dimensions and coordinates are explicit. Preimages retain complete guarded
input domains, and real limit, bound, derivative and integral selectors require
established mathematical evidence. Their descriptions do not confer convergence,
existence, invertibility or membership on an unchecked expression. Documented
lexical roles distinguish set constructors and command components.

Multivariable cards distinguish scalar and vector limits, coordinate partials,
total differentials, gradients, Jacobians, Hessians, divergence, curl and the
Laplacian. Dimensions, coordinate order and matrix orientation follow the native
signature and defining clauses. A gradient/Jacobian records coordinate partials;
it does not alone assert total differentiability. Iterated second partials use
the declared first-coordinate-then-second-coordinate order; Hessian symmetry
requires additional hypotheses. Selector help requires an established candidate
or existence proof and remains available on rejected source without presenting
that source as verified. Source-backed bowl, identity-field and oscillation
examples explain the corresponding values in both languages.

Statement records may include optional `expression_hints`: an exact UTF-8 byte
range, its original `source_text` and a semantic `reference_key`. These come
from the original typed AST observed by `SourceStatements`, independently of
the statement's proof verdict. The native tokenizer first checks that the
retained rendering agrees with its owning source header; redundant grouping is
normalized while call, tuple and interval delimiters remain significant. An
expression's source candidates must be fully accounted for by the original
AST's occurrence count on the owning line. Repeated sets, fields and calls can
therefore receive separate byte ranges. Identical brace spellings in a function
body and a list set are withheld when the counts disagree. Changed spellings
that cannot be matched and unsupported multiline layouts receive no hint.
Hints carry semantic reference cards, never declaration or proof identities;
they do not borrow a neighboring expression. No parser, AST, Runtime or
execution-state contract is changed.

The shared reader validates the original bytes again before attaching contextual
help to punctuation or unresolved field-name tokens. This covers the eight real
interval/ray forms, bounded set comprehension, enumerated sets, function values
and spaces, applications, structure types, field access and template instances
where an exact match is available. Resolved symbol declarations and individual
equality proofs keep priority. Editing invalidates these positions, and older
exports retain their existing help without a guessed expression map. Contextual
punctuation does not create extra keyword-selection buttons or a standing pane.

Semantic documentation describes mathematical conditions without establishing
an instance. For example, injectivity takes explicit `(A, B, f)` arguments;
divisibility uses dividend first and divisor second. The removed spellings
`fn_eq`, `fn_eq_in`, `is_cart` and `is_tuple` are labeled as removed rather than
documented as supported predicates. Syntax patterns in reference cards are not
claimed as verified examples; existing checked tutorial examples remain attached
to their corresponding keyword cards.

`ProofBlockBodyFailed` retains its completed `prior_steps`, actual failed
statement and execution result. The reading observer maps these results to
unique, exactly matching
original AST child under the current source parent. The failed child's verdict
and failure details are source-addressable; unmatched or synthetic statements
retain raw evidence. Following steps remain unexecuted. Prefix results from a
failed body stay in the retained native scope, or in an explicitly marked
reading-only lexical scope when the caller did not retain its environment.
Goal-WD and conclusion failures do not manufacture failed body-step records.
When the enclosing body result references an exactly parented failed child on
the same source row, the row shows the child's report once. The enclosing
failure retains its statement identity; older or incomplete mappings keep their
available reports rather than guessing which one to suppress.

Entered case failures retain `ByCasesBranchFailure`: the actual checked
assumption, its store/inference result, the entered failure stage and the
detached local environment returned by the existing scope API. The observer
shows this assumption at the case header and in matching failed-step/header
cards. Local facts remain local; a rejected case statement publishes no common
conclusion. An assumption-introduction failure does not certify an entered
case. Original `case_contexts` metadata separately records source conditions,
header spans and ordered body spans; source syntax is never a substitute for
stored assumptions or a runtime scope certificate. Old bundles keep their
available native evidence without inventing missing context. Retained evidence
does not change checking, storage, scope exit, rollback or mathematical IDs.

If a later case fails, `ExecByCasesStmtFailed::Branch` also retains the already
completed goal-formation checks, coverage proof and earlier successful branches
in execution order. A closing-goal failure retains its already proved local
targets. Their body steps, assumptions, body-step consequences and conditional proofs stay
addressable at the original case headers and source lines. The enclosing header
can disclose why the cases cover all possibilities and distinguish completed,
failed and unexecuted cases. A shared target FactId can occur in several local
case proofs; each proof keeps its own condition and scope. These conditional
targets are not displayed as global conclusions of a rejected statement. Legacy
or incomplete records do not acquire inferred case-completion certificates.
When a subject was mentioned before its environment snapshot was visited, the
first actual environment index determines its scope. Runtime environments are
visited outermost first, then retained environments before their children. This
keeps local assumptions out of outer publication lists and preserves genuine
body seeds at their own producer, while successful outer publication remains
outer. This bookkeeping belongs only to the reading observer.
Body-statement consequences use the existing inline disclosures. Local closing-target
consequences have a separate, initially closed disclosure at their case header.
Selecting one shows the actual stored target, its owning case condition and the
specific inference rule that stored that conclusion. `ParamTypes` and
`ExpandDefinition` remain distinct; a batch containing both does not assign both
rules to every conclusion. Named definition links use matching resolved source
identities. Missing origins or rule effects cannot borrow another definition or
rule. Successful common publication and its outer inferences keep their outer
meaning; this local view does not turn them into conditional-only conclusions.
Case placement comes from the retained branch result and its exact stored-target
inference reference. The inference index can retain a reused seed's outer scope;
it does not replace that branch owner. Inferences published by the enclosing
statement stay on its own source row.

Ordinary inferred-fact selections show their actual source instance and the
specific native rule that stored the selected conclusion. Rule attribution
requires the exact producer's store/infer reference and the matching typed
store effect; a batch's list of rules is not assigned to every output. The
source and result remain distinct FactIds. A one-way consequence is not
replaced by the full defining equivalence. Named-definition navigation also
requires matching declaration identity. Native checks and fact citations used
by the rule are available in an initially closed conditions disclosure, so a
nonzero-factor cancellation exposes its nonzero certificate. Storage is not
presented as another verification or a new WD proof.

The same rule renderer serves local case consequences without changing their
conditional scope. Negated-universal consequences retain their specialized
quantifier-negation explanation and identity checks. Incomplete or conflicting
source, rule, storage or scope records receive an explicit incomplete-record
message; they do not acquire a neighboring definition or guessed proof.

## Logical actions beside the source

Failed ordinary universals already retain `VerifyForallFactFailed::FailToSearchProof`.
The viewer uses its actual introduced parameters, assumed premises, locally
proved clauses, failing index and detached scope. Header and failing-clause
previews retain that context; completed clauses have local proof links and a
closed prefix disclosure. Hovering a completed clause opens its own proof
directly, including local context and a closed formation tail; it does not add
another folded copy of the formula. A failed or unchecked clause gains no proof, and the
whole universal is not published. Local premise consequences retain their own
inference rules. Missing or foreign records cannot supply inferred hypotheses;
an incomplete prefix does not erase separately verified context records.

Following a citation or scope link from a source preview records that preview's
mathematical focus, including the source position. Back restores its explanation
without inheriting an older error, keyword, reference or equality-step selection.
This uses the existing viewer history; it adds no proof or runtime state.

The failing clause's native identity also locates failures inside expression
formation. For an enclosing failed body, the reader follows only validated
parent/child execution records to the precise inner failure. This keeps outer
headers, inner headers and the actual error row distinct without duplicated
diagnostics. Native verification and failure payloads are unchanged.

Failed claims retain `ExecClaimLocalFailure`: the original claim, completed
goal-formation checks, a typed body-failure prefix and the detached local
environment returned by the existing scope API. Quantified failures distinguish
parameter introduction, premise formation, body execution and conclusion
checks. Completed body steps and earlier conclusion checks remain addressable;
the failed step is rejected and the unexecuted suffix gains no proof. A final
store failure retains the completed local body and the existing store-helper
diagnostic. None of these records activates a scope or publishes the goal.
The compact Normal/Detailed failure phase and diagnostic are unchanged.

Source-adjacent failed-claim cards use these actual parameter and premise
records. Completed local conclusion checks have an initially closed disclosure
and remain distinct from a finished claim. Missing or foreign introduction,
store, subject or scope records cannot supply guessed hypotheses. An incomplete
closing-check list does not erase separately retained parameter/premise context.
Consequences of an actual local premise retain their own rule and proof links,
including when the enclosing claim fails; they remain conditional on that
premise in its retained local scope.
Legacy lexical-only failure scopes retain their existing information.

A goal-formation check can mention the same premise FactId as the actual body.
The viewer's WD normalization preserves an already retained local scope instead
of moving that body premise into the WD-only scope. File/lexical legacy
fallbacks remain available; this is presentation bookkeeping, not an Env or
Runtime scope change. Scope ownership and source visibility are independent:
WD-only mentions remain hidden until an actual source action identifies them.

Successful `by contra`, `by cases` and `claim` blocks display their actual stored
conclusions on the block header. The goal line does not become an assumption:
`by contra` shows the retained reverse assumption at `?`, with its actual local
inferences behind a collapsed count. Case conditions are attached to their own
branch scopes. Header proof previews expose coverage and each branch's closing
proof, or both sides of a contradiction. Proof cases require coverage, not
pairwise disjointness. Claim and ordinary universal proofs expose arbitrary
parameters, assumed premises and the actual conclusion checks.

These are reader views of retained typed results. Fact positions come from the
native fact AST and the source statement's byte range; command tokens validate
assumption and contradiction anchors. Local scopes come from the retained
`local_env`, never indentation. A mapped verified source fact uses its exact
source execution's scope, while local assumptions and their inferred outputs
use their recorded assumption scope. The original bundle is not rewritten.
Missing identities, scope ownership or source anchors do not create guessed
facts. Rejected blocks get no successful conclusion arrows.

Hovering local actions or facts softly marks their actual context. The same
proof preview retains the independent symbol compartment, keyboard access,
pinning, citation navigation and edit invalidation. Inference labels show only
`Consequences n ▸` until opened. A repeated source step uses the selected
execution record; if native executions reuse a FactId, its proof remains
addressed by the execution statement rather than manufacturing another fact or
borrowing the first execution's scope. Source line selection keeps the existing
execution chooser accessible.

Ordinary and strong induction expose separate base and successor contexts,
their actual assumptions and instantiated conclusion proofs. Strong induction
retains the universal hypothesis over every integer from the starting value
through the current parameter. A shared proof body keeps separate execution
choices labelled by phase. Finite enumeration and `by for` expose each native
assignment separately, distinguish proved instances from vacuous implications
whose antecedent was refuted, and retain empty-domain vacuity.

The three witness forms expose actual local witness equalities, body or
membership checks, and the separate uniqueness obligation for `exist!`.
Successful universal `claim` results also retain a final closed formation
section. Its goal-WD scope is distinct from the proof-body scope. The observer
checks the source/return owner and retained parameter, premise and conclusion
correspondence before showing that certificate. Shared certificate nodes may
be reused without being mistaken for a cycle; incomplete or conflicting records
receive an explicit incomplete view. Formation does not prove the conclusions.

Parameter-domain and expression checks remain last and closed. Local bindings
link to the witness invocation rather than borrowing the predicate definition's
source position. These are retained execution explanations; they do not add
new proof routes or extend unsupported witness forms.

Optional statement `block_anchors` locate structured induction titles. Each
entry contains a role (`induction_base` or `induction_step`), physical line,
exact UTF-8 byte range and original source text. The reading observer derives
them from the original native TokenBlock hierarchy after checking the typed
statement and source header. They carry no mathematical evidence or FactId.
The viewer checks their ranges and tokens; old or conflicting metadata omits
title annotations while retained stages remain available from the goal/header.

These adapters have per-form acceptance examples rather than a claim about
every possible nested or legacy shape. Source-position details and internal
atomic proof routes also need further acceptance; keyword help alone does not
establish logical-view coverage.

The Zorn, Choice and Regularity views separate the foundation principle from
its verified applicability premises and actual existential publication. Local
proof steps retain their native scope. A retained obligation may verify while
its subsequent local store fails; that error is not converted into a stored
fact. The final publication is separate from these local stages.
The simple predicate names in a Zorn header use the same file/module reference
resolution as ordinary predicate applications. Its interface checker retains
the existing exact domain and defining-form requirements.

`eval` displays its actual rewrite citations, rewritten expression, exact value
and published source-to-value equality. Function applications, checked algorithm
equations, finite folds and scalar matrix computations stay in closed trace
disclosures. A fold retains its enumeration/bounds, optional seed, term values
and accumulations, including the empty sum/product identities. The final closed
WD disclosure reads the source, call and result checks. These views perform no
fresh evaluation or proof search. Qualified algorithm evaluation resolves the
existing export/module identity through the shared definition lookup; it does
not discard qualifiers or change source-WD and equation-check permissions.
Calls into an imported chapter still need its released function interface in
the caller's proof context; importing the chapter does not silently publish all
its local facts. The qualified-call regression uses explicit `release obj def`
before evaluating the imported algorithms.

Rejected `eval` commands have computation-specific explanations owned by their
actual typed dispatcher and source record. Unsupported expressions, numerical
failure, algorithm dispatch, depth limits, finite-aggregate budgets/ranges and
formation failures remain distinct. Reaching an evaluator limit is not a proof
of mathematical nontermination or nonexistence. Retained failed domain checks
stay in the final closed WD disclosure; missing earlier traces are not invented.
Thirteen strict sources cover seven actual failure variants and successful
result reuse. Three additional native failure variants have descriptions but
no certified ordinary-source positive example; this is not all-branch coverage.

Object introductions have source-row explanations for `let`, arbitrary typed
`have`, typed equalities, `have` by existence, both `obtain` forms, function
preimages and replacement images. The views use actual ordered stores and
their producer identities. An existential variable-to-witness-name mapping is
displayed as a naming correspondence, never as a new equality about a free
variable. Predicate arguments and existential variables are shown separately.
Preimage views retain the selected function interface, complete argument
groups, input domains and additional stored conditions. Replacement remains an
explicit application of the Axiom of Replacement, with its actual
single-valuedness citation and introduction/elimination properties.

Real one-layer struct auto-opening is retained separately from the declaration's
main type/equality stores. Its properties start collapsed and link the resolved
struct definition. Only layers whose object matches a declared symbol can
contribute properties or inferences; type-preflight layers remain temporary.

Internal WD assumptions are hidden using their retained local stores, even
when an older fact-directory entry reports an outer scope. Actual successful
introduction stores restore the declaration properties; a body condition
guaranteed by existence is not labelled as an assumption. Its real inference
outputs stay at that body's native source row, separate from preflight
inferences. Property links and symbol information navigate to the actual
introduction. Repeated source lines follow the currently selected native
scope across adjacent statements; they do not silently return to the first
execution. Missing or conflicting source, symbol, store, interface or proof
records do not produce guessed properties or bindings.

Six function/algorithm definition forms have source-local definition checks:
formula, piecewise, unique-existence and inductive functions, plus algorithms by
cases or induction. Function guards are local input assumptions; their WD
preflight stores cannot become proved facts at the definition row. Formula
definitions retain the actual return-membership proof. An independently empty
complete input domain makes that return obligation vacuous, without proving a
standalone false membership or skipping expression WD.

Piecewise headers expose actual coverage and pairwise disjointness certificates;
each native `case` position exposes its local conditions and return check.
Nested recursive cases keep their enclosing scopes, integer measure, lower
bound and restricted recursive interface. Unique-existence definitions show
the checked source proposition and the three retained function properties.
Actual case-equation outputs navigate to the matched source branch. Executable
algorithm registration is distinguished from evaluating a concrete call.
Missing conditions, mismatched pairs, scopes or store identities remain
explicitly incomplete. These views do not reclassify an enclosing template as
a separately exported function statement, or hide an actual failed evaluation
in a module whose preceding definitions were accepted.

Seven extensionality and explicit-release forms have source-local proof views.
`by extension` retains both checked subset directions. `by fn_extension` shows
the complete input interfaces, their actual comparison and the pointwise
universal proof or its known-universal citation. Returned functions retain
their separate application layers. Neither a few equal values nor a partial
input interface substitutes for the native domain certificate.

Object and struct releases link to the original definition and list only the
actual publication stores. A retained `TrustHave` origin remains explicit;
releasing a definition does not turn an assumption into a proof. Cartesian
release shows the checked defining equality. Tuple release distinguishes a
known tuple value from Cartesian membership, follows the checked finite shape
and index domain, and retains the native `fn_set_member` requirements and
coordinate proofs. Empty tuples have no coordinate obligations. Range
expansion displays possible values as a disjunction, including singleton
ranges, rather than claiming every alternative simultaneously.

Published properties are collapsed by default. Their real inference batches
belong to the release header; WD-only temporary stores remain hidden even when
their event reports an outer scope. Existing FactIds and producers are
preserved. Expression WD remains the final closed section; missing or
conflicting domain, shape, source, store or proof correspondence is reported
without inventing evidence.

Rejected releases and extensionality commands use the retained typed failure
stage, rather than a generic unproved-conclusion message. Tuple shape, input
domain and coordinate checks, unavailable structural definitions, parameter
release restrictions, Cartesian equality formation, range membership, subset
directions and function-domain/pointwise checks remain distinct. A retained
failed target is an obligation, not a published fact. A proof-body failure can
link to its completed local prefix and exact stopping statement; returning
preserves the selected command. Retained expression formation is last and
initially closed, including for internal command targets without their own
source line.

An empty function-domain comparison list is valid but supplies no candidate
comparison. A missing list is incomplete. Failure to construct a pointwise
target does not itself supply a domain-matching proof. Earlier checks or local
environments omitted by the producer remain unavailable; the reader neither
reconstructs them nor treats a successful local prefix as an outer conclusion.
See `web/tests/expansion-failures.cjs` for actual-source coverage and missing-data
controls. This observer coverage does not establish every internal enum branch.

Rejected applications of regularity, choice and Zorn's lemma also have typed
source-local explanations. Input formation, predicate-interface validation,
an interrupted auxiliary proof, an unmet applicability premise and conclusion
publication remain distinct stages. The retained failed premise is displayed
as an obligation, not a stored fact; the principle itself is identified as a
set-theoretic foundation rather than a theorem proved by these checks.
Current-failure expression checks appear last and initially closed. Missing
earlier applicability checks and local storage histories are not reconstructed.

For these commands, a retained completed proof-body prefix can contain a native
execution result whose corresponding source row remains `not_exported`. The
reader shows the retained result and reports the unavailable source/execution
correspondence. It does not change the row's status or invent a jump. The
actual rejected child remains navigable, with exact return to the command.
`web/tests/foundation-failures.cjs` covers the observed stages, local partial
applications and repeated successful executions. The three internal `Store`
failure branches still lack ordinary-source acceptance; this is not full
result-enum or full-language coverage.

Rejected ordinary/strong induction and finite/range enumeration use their
retained process stage. A failed integer-start check, goal formation, base-case
goal, induction-step goal, auxiliary-body step, finite-domain check and
enumerated instance are distinct. Instantiated failed goals remain obligations,
not stored facts. An assignment ordinal is shown only when recorded; the reader
does not recover parameter bindings from the displayed goal or regenerate
induction hypotheses and prior successful cases.

Proof-body correspondence is checked by the same private helper as explicit
expansion and foundation failures. Real completed-prefix references and the
actual rejected child retain their navigation; inline native results without
source execution records keep an explicit limitation. No source status, fact
identity, scope or default selection address changes. Retained current-failure
formation is last and initially closed. Quantified formation uses its actual
local failure envelope and the existing formation checker rather than treating
temporary checking parameters as proved assumptions. See
`web/tests/process-failures.cjs` for the 20 observed route/stage combinations.
Internal assumption/domain/storage/instantiation and unwired branches without
ordinary-source evidence remain uncertified. Malformed structured induction
is rejected at parse and does not certify an executor `BodyShape` branch.

Failed function definitions have dedicated source explanations for expression,
case-based, recursive and unique-existence forms, including the two algorithm
wrappers. Anonymous-function failures distinguish parameter domains, input
conditions, return domains, body formation and body membership in the return
domain. Case definitions distinguish coverage, disjointness and each branch's
body/return check. Recursive definitions additionally distinguish measure and
lower-bound formation, integrality, lower-bound comparison and retained nested
branch paths. An algorithm's actual `DefineFn` failure retains the underlying
function-definition stage; it is not presented as a completed registration.

Only recorded goals, branch indices and nested paths are shown. Disjointness
failures carry a pair of indices but no failed proof certificate. Earlier
successful branches, parameter bindings and complete local checking histories
are not reconstructed. Current-failure expression checks remain final and
initially closed. The source-forall check for `have fn ... by exist!` remains an
unproved prerequisite when it fails, with no function interface published.
A later call with the wrong arity does not turn an accepted definition into a
failed definition. See `web/tests/function-definition-failures.cjs` for the
24 observed route/stage combinations and ordinary/registered/local/repeated
controls. Name clashes, empty/mismatched case lists, rare interface/property
failures and other unobserved internal variants still require source evidence.

Object symbol hover and selection reuse the actual declaration's introduction
record. A given-value declaration explains its value; it is not described as
choosing an arbitrary element. Trusted objects retain their explicit assumption
origin, and real structural parameters and failed-check temporaries retain their
local scope. Structural domains and laws remain grouped, closed and citable;
the symbol's domain is not repeated in a second generic summary. Ambiguous or
foreign execution identities do not borrow another declaration's properties.
Virtual Eval source labels read **Current input**, while actual filenames and
authored source titles remain intact. This changes labels, not source identity.

Six mathematical-interface definitions have source-local logical views.
Predicate clauses are defining conditions, not proofs of instances;
`abstract_prop` declares untyped argument names and arity without invented
domains or a defining equivalence. Theorems retain their actual goal proof and
publication stores. Strategies retain their proved parameter/premise interface
without ordinary known-universal publication.

Struct headers show ordered field domains and conditions without claiming an
instance exists. Optional `structure_field` entries in `block_anchors` retain
the original UTF-8 ranges, typed binding identities and field indices. They are
validated against the original token block, rather than retokenizing a rendered
header lacking its body. Old bundles keep the field information at the header;
missing, duplicate or conflicting anchors never guess another field's line.

Template parameters and premises remain local while the actual publication
records retain all quantified binders and source-fact links. Its body execution
reuses the existing object/function/assumption explanations at the native body
position, under the original template owner and local scope; it does not
fabricate an inner source Stmt or relabel the template header. A premise written
on that same header is included once. Definition-body checks, field checks and
proof premises stay distinct; formation remains the final closed disclosure.
Name display distinguishes the template's retained local defining placeholder
from competing public declarations. Only its exact resolved family can lose an
internal export prefix; real shadows and other public definitions retain the
existing ambiguity boundary.

Template body cards list their actual arbitrary parameters and adopted premises,
with links to the original local facts. Consequences of those assumptions retain
their own inference rule and definition links, start closed, and share the
template header's source row. Structural parameters expose their checked local
structure properties separately. Conditional family properties remain distinct
from these local assumptions. An entered failed template retains only the
premise prefix it actually adopted; a later failed condition and an unexecuted
body acquire no assumption or proof. Body type preflight remains a separate
scope. Set-kind fact references use the same mathematical phrasing as quantified
expressions, rather than exposing internal predicate spellings.

Reflexive, symmetric and transitive registration expose the actual verified
universal law and link to the resolved predicate definition. Registration
installs a usable property; it does not separately publish a universal fact or
assume arbitrary instances. Its local parameter/premise scopes come from the
retained universal proof.

`trust`, `trust have` and `axiom` explicitly distinguish accepted assumptions
from proved facts. Their actual stores are collapsed at the source header;
body conditions and inferred consequences keep their own source positions.
`trust have` does not claim an existence proof. Later fact reuse retains its
native trust dependency, and releasing a trusted object's definition keeps the
`TrustHave` assumption origin. Strict-policy rejection remains distinct from
syntax, formation and truth-verification failures; the reader changes none of
those policies. `sketch` exposes its checked local steps without publishing
objects, definitions or facts to the parent scope. Its body keeps a source-local
scope reminder, without a fabricated closing goal or WD certificate.

`by thm` and `release thm` have separate language-help and application views.
The application view uses the successful execution's resolved callee, actual
arguments, premise proofs and direct stored conclusion identities. User theorem
parameters are paired with arguments from that same captured declaration;
builtin calls show their arguments without inventing formal parameter names.
Theorem links navigate to the resolved declaration. `by thm` exposes its exact
selected-conclusion proof on demand; `release thm` displays its directly returned
conclusions at the invocation's source row, including generated existentials.
Parameter and expression checks remain in the final closed disclosure. Later
reuse of a conclusion keeps its own citation route, rather than borrowing the
producer's entire theorem application. Missing records and failed applications
receive no fabricated bindings or successful-application explanation. This
adapter does not yet explain every internal theorem derivation or complete
function-domain source construction step by step.

Native matrix function membership explains the captured construction body,
its existing and required complete input interfaces, and the scalar-range
evidence separately. The five native scalar sources distinguish real constants,
real input matrices, real operands, a returned real-valued function and a
complex-valued interface. A complex interface does not assert that entries
are non-real. Equality aliases follow their retained path and fact identities;
local input premises stay in their original proof scope. Matrix-space reduction
opens the actual corresponding function-membership proof. The accepted native
rule owns the domain-renaming and standard-scalar inclusion checks: this result
does not retain a separate domain-comparison or subset FactId, and the viewer
does not manufacture one. Expression formation remains last and closed;
`ParentAtomic` is not presented as an independent WD certificate. These views
do not yet cover every matrix application, scalar or equality proof family.

The final formation disclosure now opens the actual complete-domain checks for
`fn_set_member`, `cart_member_from_coordinates` and
`tuple_equal_from_coordinates`. It retains the existing interface, required
inputs, parameter/guard correspondence and native alpha-renaming or two
verified inclusion proofs. Named function definitions, existing memberships,
finite functions, compositions, templates, returned functions, matrices and
multivariable selectors keep their native interface sources and citations.

Ordinary function-space membership also requires the complete input domain,
followed by the return-value conditions. Its source bubble separates these two
mathematical obligations and shows their retained proofs. Cartesian membership
uses the actual product-identification proof and each coordinate's factor
membership. The native function-membership strategy, Cartesian strategy and
Cartesian builtin rule retain their distinct owners. Nested universal premises
keep their bound variables and citations inside their own proof; they are not
flattened into the enclosing statement's context. Missing or foreign domain and
condition records receive an incomplete-evidence notice. Expression checks stay
last and closed. These views do not reconstruct discarded failed-search traces,
and a search miss is not a proof that the membership is false.

Rejected multiline statements have a muted status at their own source header,
separate from the red marker at the actual failure. Both views reference the
same native rejection. A retained body-step reference identifies the exact
failed child, including nested blocks and case indices; its source link returns
to the same header issue. Captured goals are optional and closed by default.
An owning typed goal uses the mathematical formatter; a text-only captured goal
stays complete Litex, without parsing a second mathematical model from its
string. Missing source spans or foreign child records never justify a guessed
step or jump. Failed goals and local assumptions are not shown as established
outer results. Pointer, keyword, keyboard and edit-invalidation behavior remains
source-adjacent.
Generated comparison binders can be paired even when they have no source token.
Tuple equality displays the required index domain and the actual interfaces of
both peers. Its internal real-return placeholder is not a coordinate-value
requirement; complex-valued tuples remain valid examples.

Domain failures distinguish unavailable complete interfaces, function/target
formation, parameter-count mismatches and failed inclusion directions. A
completed first inclusion remains inspectable when the reverse fails. Failure
records do not retain the original complete target interface, so the viewer
shows only their recorded source candidates and obligations. It does not infer
an interface from source strings, label an unproved inclusion false or present
a return-range premise failure as an input-domain mismatch. Cross-file examples
explicitly release a named function definition before using its defining
equality; this presentation change does not alter module publication rules.
Exported names and retained provisional defining names are treated as the same
declaration only when their actual declaration reference and remaining body
agree. Unloaded or ambiguous exports keep their configured public namespace;
internal file prefixes and safely identified generated comparison binders are
not presented as mathematical names. These changes affect display only.

A verified `forall ... <=>:` has a source-header entry for the two implications.
Shared premises remain separate from the left and right sides: each side is a
premise in one direction and a goal in the other, not an unconditional source
fact. The viewer consumes the actual two direction proofs and their separately
stored universal identities; proof-goal IDs are not merged with saved IDs.
Following a later citation opens the direction actually cited. Direction proofs,
published results and the final direction-specific formation checks are
collapsed. Retained partial failures distinguish an established first direction
from a failed or unexecuted second direction, without publishing an equivalence.
The owning statement's retained explicit-assumption dependencies remain visible
at the header and when following a saved direction.
Quantified shared premises are explicitly grouped before the outer implication.
The original iff has no invented whole-expression WD certificate: the final
disclosure shows each direction's retained checks under its own premises.

`not forall` explains its retained counterexample existential and the actual
proof of that existence. Shared premises and the native Boolean form of the
negated conclusion remain intact: refuting a conjunction needs at least one
failed condition, while refuting a disjunction requires each disjunct to fail.
Source-clause hints describe the formula's roles rather than asserting its
conditions independently. Known existence, builtin and universal applications
retain their own citations and bindings. A witness is shown through its actual
construction; an existence proof does not introduce a new named object.

The existential checked during verification and the fresh existential later
stored by `InferNotForallFactResult` have distinct identities. Both remain
inspectable, and later reuse follows the actual stored inference. Inferences
from a local `not forall` assumption remain explicitly conditional on that
assumption and stay within its scope. The final closed formation disclosure
uses the counterexample's retained parameter and
body-expression checks; it does not invent a separate original-universal
certificate. Rejection, missing records and private formation assumptions stay
distinct from proved or published facts. Cross-file examples use named theorem
interfaces and explicit release under the existing module publication rules.

This module connects the source to its actual verification evidence, so readers
can follow citations back to facts, definitions and rules. Concept highlighting
follows resolved symbol identity, separately from proof dependencies.

Conjunction and disjunction explanations consume their native verification
records. A conjunction shows each checked component, or the actual universal
instance that supplies the whole conjunction. Selecting a stored component
opens that component's proof. Partial failures retain the accepted prefix and
the failed component without treating the whole conjunction as established.
The whole-conjunction universal route does not retain independent component WD
certificates; the final closed formation disclosure states that limitation.

A disjunction distinguishes a locally selected branch, reuse of a stored
disjunction with argument-equality certificates, universal instantiation and
builtin coverage rules. Temporary negations of other branches are labelled as
local hypotheses, including when followed as citations. Discharging them
establishes the whole disjunction, not its individual branches. A direct branch
proof need not negate the other branches. Builtin rules retain their own names,
bilingual comments and actual conditions; coverage does not assert that the
branches are disjoint or choose a true one. Integer-range rules retain their
interval and real carrier-equality citations. Expression formation is checked
for every alternative, even if another alternative is true. Missing branch,
scope, citation or equality records are never reconstructed from source text.

Hover anywhere in a mapped fact's source row for a transient proof preview;
focusing its line number provides the same keyboard access. The sentence owns
the initial dwell timer and proof content: moving between its tokens neither
restarts that timer nor rebuilds the proof. Hovering an object, predicate,
operation or keyword adds a separate symbol-information compartment to the same
preview. Changing symbols preserves expanded proof conditions and scroll
position. The last symbol information remains available while entering the
card; both compartments scroll independently and stack on narrow screens.
Entering the card cancels delayed dismissal and incidental pending previews
from crossing neighboring sentences. Outside facts, symbols retain standalone
semantic help. Definitions and proofs still follow their separate recorded
identities; hovering an object does not select it as the conclusion.
The preview follows that primary fact's own evidence and exact source line,
including conclusions nested inside a larger proof. Its premise links navigate
to actual FactIds. Symbol help uses the same renderer inside and outside proofs.
Mathematical premises are visible first; parameter and expression conditions
remain available in a disclosure. Verified chains expose their adjacent steps
from the recorded result, rather than treating the enclosing statement's entire
citation list as the proof of each line. Hypotheses are labeled as hypotheses.
Moving away, Escape, editing, navigation or closing the preview dismisses it.
Unchecked or unmapped lines do not receive guessed proof evidence. Missing
fact-specific proof steps are stated explicitly; authored summaries currently
cover selected proof forms, not every kernel rule. JSON remains the underlying
evidence format; the reader has no raw JSON column or JSON-view toggle. Source
hover and on-demand explanations expose definitions, citations and inferred
results directly beside the mathematics.

Proof explanations connect their cited context with the actual rule application.
The rule's exact recorded name is visible, together with its catalogue statement
when available. Builtin strategies and structural membership derivations retain
their own names and categories. For example, `p / 2 $in Z` in the sqrt-two lesson
uses `ExactIntegerDiv`: the context supplies integer membership and divisibility,
and enclosing expression verification owns the nonzero-denominator requirement.
The card gives the guarded integer-quotient law and the substitution `a = p,
b = 2`. It does not claim that the distinct `ExactIntegerQuotient` fallback was
called. Application selection follows the current proof's typed wrapper chain,
not a recursive collection of rules from premises, WD or earlier statements.
Consequently each equality step retains its own rule. Missing catalogue text
does not erase a retained application name; catalogue presence alone does not
establish an application. Assumptions and rejected statements receive no
successful-rule label. Hover and pinned views use the same formatter.

Atomic proof applications expose four complementary routes. Known-fact reuse
links the precise cited fact and pairs its arguments with the current arguments
using the recorded equality certificates; changed arguments are visible by
default. Builtin rules and builtin strategies show their actual name, retained
requirements and current conclusion. A `forall` application identifies the exact
universal fact, lists parameter substitutions in declaration order, and presents
the already-instantiated premises with their matching proofs. Parameter domains
and conclusion-argument matching remain available separately. The viewer never
substitutes source strings to construct those premises.

Named strategies show the recorded strategy name and bindings recovered from
typed parameter identities and argument-match records. They do not acquire a
guessed definition link: current detailed records do not retain a resolved
strategy-declaration identity. Missing parameter lists, unmatched proof identities
or incomplete records receive explicit explanations rather than invented
correspondences. Reference navigation and return retain the selected application.

Function-definition proofs show the retained defining equality, parameter-to-
argument bindings and each checked body expansion in execution order. For
`reciprocal(2) = 1 / 2`, the current verifier uses `ByObjectDefinition`, not
`ByKnownSpecialProperty`: the card shows `x = 2`, the instantiated body, and
whether the remaining equality is identity or needs a separate proof. Nested
applications and both-side normalization use the same evidence adapter. Function
aliases follow the recorded equality endpoint, which may have different binder
names from the original declaration; source text is never substituted to guess
a body. Retained body-domain checks join the final closed WD disclosure, including
when a selected body has a narrower domain than its callable signature.

User-predicate definition applications link the resolved declaration and pair
its typed binders with the actual arguments; the existing requirement/proof
pairs explain the instantiated conditions. Selected special-property adapters
explain tuple coordinates, tuple reconstruction and function codomains using
their actual certificates. Known equality paths expose their ordered edges and
any separately checked connecting equality. Unsupported forms and incomplete
records keep explicit missing-data explanations; these adapters do not cover
every template, matrix, induction or special-property proof form.

Equality operators have their own proof targets when retained evidence maps
them precisely. In `a = b = c`, hovering the first `=` explains only `a = b`;
the second explains only `b = c`, with that step's own mathematical citations
and parameter conditions. Focus or click the operator to inspect it, or use
the preview's **Keep open** action; in the editable overlay, Ctrl/Cmd-click
selects that step while ordinary clicks still position the text caret. Normal
line selection returns to the complete chain. Source rows and inferred results
are unchanged.

The binding uses `VerifyChainFactSuccess.adjacent`, `ChainFact.objs` and
`prop_names`, the same adjacent verification results read by Normal JSON's
chain projection. Exact tokenizer byte spans locate the source operators;
nested parentheses, brackets, braces and tokenizer-excluded comments do not
consume chain positions. The complete top-level operator sequence and typed
operand identities must agree. A supported standalone verified equality uses
its own `VerifyEqualitySuccess` in the same way. Multiple possible primary
facts, missing evidence/tokens, mismatched counts or identities, and unsupported
multiline/nested source mappings receive no guessed operator proof. Existing
whole-chain previews and language help remain available. Some proof forms
still have only a general explanation plus retained citations.

For example, syllogism fact `f5` cites universal fact `f4` and hypothesis `f1`;
domain condition `f9` remains separately accessible in the proof preview.
Captured statements inside `by contra` keep their individual source identity
and evidence. The sqrt-two goal and terminal `impossible` do not currently have
independent statement records; removing the raw view does not add evidence for
unmapped lines or change the underlying reading JSON/export contracts.

Quantified fact references use retained `ForallFact` and `TypedParameterGroup`
structure to render their binders in natural language: Chinese uses
`对于任意集合 X`, `对于任意非空集合 X`, and `对于任意有限集合 X`;
English uses `For every set X`, `For every nonempty set X`, and
`For every finite set X`. Ordinary domains retain membership, such as
`对于任意 x ∈ ℝ` / `For every x ∈ ℝ`. Source keeps the keyword `forall`.
Grouped names, dependent domains,
nested scopes, premises and conclusions are preserved. English uses set-kind
annotations in English. Missing or unsupported structure keeps the complete
original formula instead of guessing a quantifier header from its text.

Proof previews show concrete universal instantiations when the retained proof
contains an ordered argument list and its cited quantified fact. For example,
the syllogism displays `person = socrates`; the same component displays
`a = 72, b = 84, c = 96` in the least-squares example. Incomplete metadata or
an arity mismatch retains the general explanation rather than inventing a
substitution. Hover and selected-source views use the same proof content.
The preview's **Keep open** action fixes that explanation beside the source.
Fact line numbers indicate this entry point; keyboard users can focus a line
number and use Tab or Right Arrow to enter its open preview.

Grey inline inference buttons preview one complete retained result and show
the number of additional results. Visual ellipsis does not shorten the stored
formula, remove clauses or discard FactIds: opening the button shows every
published result. The source retains its original rows. Supported generated
existential facts use fresh local mathematical witness names, such as `k`,
instead of internal binder names. This display-only substitution uses retained
symbol identities, avoids free and bound names, preserves existence/unique
existence/nonexistence, and leaves authored source names unchanged. Ambiguous
identities or unsupported structures retain the complete original formula.

Local facts identify their recorded enclosing proof and distinguish assumptions
from conclusions established under those assumptions. Current scope metadata
does not identify every nested lexical range; the viewer does not invent scope
brackets from indentation. These are shared reader behaviors, independent of
problem-specific commentary or exercises.

## Current status

The initial implementation provides a typed reading projection, a shared
browser viewer, loopback preview/upload, JSON output and static export.
It reads actual execution results; it does not reconstruct dependencies from
localized verifier messages or search for a different proof.

```sh
litex -reading
litex -reading -f chapter.lit
litex -reading -r book/
litex -reading -json -f chapter.lit > chapter.reading.json
litex -reading -export book-site -r book/
```

### Mathematical manuscript view

Add `-latex` to reading mode to start with mathematical text instead of source:

```sh
litex -reading -latex -strict -lang zh -f chapter.lit
litex -reading -latex -r book/
litex -reading -latex -json -f chapter.lit > chapter.reading.json
litex -reading -latex -export book-site -r book/
```

This is a reading presentation option. It uses the same native verification,
project loading, proof records and shared viewer as ordinary `-reading`.
Standalone `litex -latex` remains the separate parse-only compilation command.
`-document` belongs to that standalone command, not reading mode.

The manuscript uses the official compiler's paragraphs, proof methods and
mathematical notation. Proofs flow as continuous paragraphs with run-in case
and contradiction labels, wrapping naturally to the available width. Hover or focus a fragment
to see its exact original Litex source and the existing statement explanation.
Click to keep the popup open; follow the same native fact references or open
statement details. Escape and the close button dismiss the explanation. The
source button returns to the usual source reader/editor. Editing invalidates
old proof data and disables mathematical presentation until checking completes.
Checked primary facts with a unique matching source execution also have an
initially collapsed **Derivation** beside the sentence. Opening it lazily uses
the same native proof renderer as fact details; reopening preserves its body.
Premises remain expandable and native fact references remain navigable. The
positive-natural lower-bound rule reads as a premise-to-conclusion sentence
only when its typed goal, bound `1`, membership object and builtin positive
natural set correspond. Missing or mismatched evidence gives an explicit
unavailable explanation. Inferred facts, assumptions, rejected steps and
ambiguous executions do not borrow a primary fact's inline derivation.
Uploads and rechecks retain the selected document layout. Compiled prose keeps
the compilation language; changing the interface language does not rewrite TeX.

Mathematical bundles add `reading_layout: "latex"`. Each source can contain
`latex_blocks` with compiler `content`, the exact `source_text` snapshot and its
original byte range, plus `statements` containing original `statement_id` and
UTF-8 `start_byte` / `end_byte` spans into that compiler content. Boundaries are
recorded while the compiler composes the original typed AST; identical formulas
are never joined by a text search. Rendering does not execute statements or
change evidence, FactIds or scopes. Source chunks carry the optional layout;
the lazy manifest and source-only parts do not duplicate it. Older bundles
continue to use source presentation. `getReadingLayout()` exposes the document's
layout metadata to the upload host, independently of a temporary source view.

Missing, changed, foreign or malformed source mappings, an unavailable math
engine, or unsupported document typography retain the original source. Rejected
and unexecuted statements keep their native statuses. Ordinary rejected steps
do not necessarily stop later checks; a parse termination can leave an unparsed
suffix, which remains available as source. The view does not confer proof on
displayed mathematics or add explanations missing from ordinary reading data.
The existing cross-file function-evaluation boundary is preserved, including
the namespaced `alpha::twice(2) = 4` rejection in the focused fixture; presentation
must not turn that native rejection into a success.

Focused acceptance uses `tests/reading_latex.rs`, the reading/HTTP/LaTeX CLI
contracts, and `web/tests/latex-mode.py` / `latex-mode.cjs`. The producer and shared
viewer exercise all 52 current statement fixtures; this is layout and source-map
coverage, not a claim of complete mathematical explanation coverage.
The focused acceptance receipt is
[`tests/fixtures/reading_latex_acceptance.json`](../../tests/fixtures/reading_latex_acceptance.json).

For a complete mathematical demo, use
`litex -reading -latex -strict -lang zh -r examples/reading/homepage`.
The [homepage collection](../../examples/reading/homepage/README.md) includes
least squares, sets, Newton iteration, irrationality of √2 and Cantor's theorem.

Preview opens a browser; `-no-browser` prints the URL without opening one.
Use `-port 49181` to choose a port, `-lang zh` for Chinese presentation and
`-strict` to use the verifier's strict execution policy. File/project inputs
use the existing project loader. `-e` uses isolated source evaluation.
Bare preview accepts `.lit` files, a complete project folder, or an existing
reading JSON bundle. A dependent source needs its project configuration and
dependencies. The local service listens only on `127.0.0.1`.

The viewer follows the typography and palette of `../litex-webpage`: a light
background, green controls, blue current statements, green cited facts and
purple concepts. A selected `prop` shows its full predicate application, then
⇔ beside a grouped block containing every argument type and all complete
defining conditions. Short clauses share a row, with each conjunction kept
with its following clause; longer formulas retain their mathematical layout.
Repeated instantiated conditions retain their separate fact links. There is
no prose or separate domain heading. This is the
reading form of the declared typed interface; quantified conditions retain
their whole scope. Click the source keyword `prop` for the
purpose/semantics guide and its checked short example. Source keyword help
supports Enter/Space; Escape returns focus to its keyword. A new statement
selection restores mathematical content. The contextual explanation’s type caption is plain
text. Usage hints, the color legend and record explanation live in the footer’s
Reading help disclosure. Small file-local reference counts appear at every explicit declaration;
its occurrence list starts closed. Hover/focus uses resolved definition spans
and typed parameter evidence to show the exact binding line and declared domain,
including quantified parameters and shadowed names. Later inferred memberships
do not replace that domain; missing evidence does not trigger a text guess.

The detail pane omits duplicate source, engine versions, file/line metadata,
proof trees and a default rule catalogue. Source concepts and real fact
citations remain clickable. Preview, static export and embedding share this
viewer without a Node runtime or frontend build. Bundled KaTeX and embedded
WOFF2 fonts work offline; see web/vendor/katex/README.md for version/license
and deterministic regeneration. Rendering disables trusted HTML/URL commands.

Reading controls use a closed “Reading records” disclosure instead of visible
JSON import/download buttons. The primary action is “Open a file”; there is no
download control. It explains that records save how each statement
was checked, which facts it used and what it inferred; JSON is described as the
file format. Folder opening, when available, stays inside. The chapter directory starts closed,
and Back appears after navigation. The shell supplies optional `onOpenFiles` and
`onOpenProject` callbacks; the shared component owns the controls. File inputs and upload validation remain shell responsibilities.

Optional schema-v2 `statement_kind` retains the real tagged AST path. Optional
`declaration_symbol_ids` identifies direct named declarations using captured
typed fields, excluding function parameters and nested binders. Definition-line
badges show current-file source references. Clicking a badge lists source
snippets and jumps to the exact token. Counts use resolved symbol identities
and unique UTF-8 spans, excluding the declaration itself and generated inferred
output; comments are not symbol occurrences. Repeated execution does not inflate
the count. These are source references, not proof-dependency counts.
The concept occurrence list also uses original source snippets and marks the
exact token, rather than showing execution-resolved mathematical subjects with
internal file qualifiers. Clicking navigates to that token. Authored qualified
names stay unchanged. For an unloaded chapter, its symbol name and source path
remain navigable until the chapter is loaded.
Optional `mathematics` display data comes from typed AST values and retained execution
results. Optional `mathematics.latex` contains a `subject` formula and parallel
`parameters` and `facts` arrays generated by the existing LaTeX compiler. Missing/unsupported conversion
keeps the complete retained text; it never reparses source or guesses formulas.
Ordinary quantified comparisons use structural display breaks; other logical
forms preserve the canonical compiler grouping and may scroll horizontally.
The viewer left-aligns the outer gathered comparison layout, groups parameter
commas with their formula, and aligns conjunctions beside complete clauses.
A simple two-row outer comparison without nested environments can flow inline,
so short inequalities stay on one line. Matrix/case layouts keep their original
grouping. Plain-text fallback never breaks an identifier in the middle.
Parameter-type metadata stays distinct from iff-clause metadata; the viewer
places both in the right-hand condition block of the typed predicate display.
Instantiated equivalences retain every complete definition clause, including
conjunctions and chains; they are not reconstructed from a filtered list of
published inferred outputs. Abstract predicates receive no invented definition.
The current projection covers ordinary predicate definitions/applications,
selected object declarations, function equalities and fact goals. Other forms
show actual recorded output facts where available, or an explicit unavailable
message. Older bundles remain readable without guessed mathematical meaning.
Clicking source selects the statement; result/citation buttons select the fact.
In the editor, an ordinary click only positions the caret and selects context;
Ctrl/Cmd-click performs the token's semantic action or keeps its explanation open.

Source ranges use original UTF-8 byte offsets. Syntax highlighting distinguishes
keywords, predicates, functions, objects/variables, types/sets, theorem names,
numbers/constants, operators, punctuation and comments/asides. Resolved symbol
identities, declaration kinds and typed function-head evidence determine semantic
colors; source spelling never overrides a resolved identifier. Declarations and
uses share their role. Selection/citation highlights retain priority.
`python3 src/reading/generate_highlighting.py` refreshes the inline lexical
catalogue from parser constants, analysis-property dispatch and tokenizer symbols;
`--check` detects stale vocabulary. No extra browser asset or frontend build is
required. Tokens without a specific authored explanation receive concise role
help where appropriate. Builtin set
help (for example `R`: real numbers ℝ) is keyed by resolved symbol identity,
not spelling. Tooltips support Escape and stay inside the viewport. Optional
source `tokens` records normalized tokenizer text with original UTF-8 ranges;
comments and inline asides are excluded, Unicode aliases retain their original
source spelling, and lazy exports load tokens with the chapter. Tokenization
failure leaves plain source; older bundles retain resolved-set help without
inventing lexical boundaries. This is language help, not mathematical proof
evidence. Occurrence highlighting uses resolved identities and reports mapping coverage per statement. Typed proof
payloads and retained local scopes are exported. Actual store/infer outputs
link seed facts to derived fact IDs; the reader displays one compact grey count
button beside each producing statement on the same source line, excluding temporary
definition/parameter-checking assumptions, and can follow a later citation
back to an inferred fact. Clicking the button opens an anchored popup containing
the actual results; clicking it again, clicking outside or pressing Escape
closes the popup. Escape restores button focus. Result text wraps within the
popup and stays hidden by default; the source gains no display rows.
Selecting an inferred output shows the producing predicate's complete
mathematical equivalence when retained, highlighting the selected domain or
condition. Named definition links lead to that definition's mathematical view.
Trust, failures and local-scope qualifications remain visible. Full execution
evidence and per-conclusion origins remain in JSON; optional language help
provides access to the Rule Book.
Nested proof statements
and repeated execution contexts retain separate identities. Ordinary facts
have exact source focus and hypothesis/verified/declaration roles. Actual WD
registrations and their retained formation evidence are navigable. Whole-book
exports load source/proof chapters, search and concept indexes on demand;
complete JSON and a standalone offline page remain available. The loopback
service caches identical successful closed-project uploads in bounded memory.

HTTP responses include their exact byte length. After writing a response, the
connection closes its write side before draining unread request bytes with a
250 ms deadline and a 16 MiB limit. This lets early upload rejections deliver the complete
error response without a TCP reset discarding it. No further request on that
connection is processed. `tests/reading_http.rs` checks complete responses for
rejected uploads with 64 KiB bodies, alongside normal uploads and strict policy.

Rule descriptions are shown when authored metadata
is available; a catalogue entry alone is not a complete mathematical rule
specification. [DESIGN.md](DESIGN.md) records the full target and acceptance
boundaries; this first implementation does not establish every target there.

## Website embedding

See the [integration guide](../../docs/reading.md) for schema v2 evidence DAGs,
inference records, the local upload API, component methods and iframe messages.
The [runnable host example](../../examples/reading/website/README.md) uses the
same export through both integration paths.

Publish the generated `book-site/` files alongside the website, then embed the
published page:

```html
<iframe src="/books/book-site/index.html"
        title="Interactive textbook"
        style="width:100%;height:85vh;border:0"></iframe>
```

Or load `katex.min.css` and `reader.css`, then `katex.min.js` before
`reader.js`, and mount the viewer into an existing element. Its styles are scoped to the reader; standalone page styles require
the `litex-reading-page` body class.

```js
const reader = await LitexReading.open(document.getElementById('reader'),
  '/books/book-site/reading.manifest.json', { locale: 'zh' });
```

Static browsing uses the exported evidence and needs no running Litex process.
The loopback preview URL belongs to the local machine; publish the export to
make it available to website visitors. Rechecking edited source requires a
separate execution endpoint; mounting the viewer does not install one.

## Ownership

The reading subsystem owns the exported reading model, its projection
from checked results, source/occurrence mappings, rule catalogue export,
and the reusable browser viewer and its assets. Local preview and published
websites should consume the same model and viewer.

Existing components retain their responsibilities:

- [run](../run/README.md) and [run_module](../run_module/README.md) load and
  execute sources in their real project context.
- [execute](../execute/README.md) and
  [store_fact_and_infer](../store_fact_and_infer/README.md) produce typed
  verification, storage and inference evidence.
- [json_output](../json_output/README.md) retains its current Normal, Compact
  and Detailed contracts. Reading is a separate projection of the typed
  evidence, without decoding localized JSON or replacing the evidence owners.
- [identifier_identity.md](../identifier_identity.md) defines symbol identity;
  [TokenBlock](../tokenize/token_block.rs) retains original token byte ranges.

CLI dispatch in the existing launch/run layers delegates reading work here.
Reading must preserve statement transactions,
scope visibility, source order and explicit trust boundaries.

## Maintaining the projection and catalogue

```sh
python3 src/reading/generate_capture.py
python3 src/reading/generate_capture.py --check
cargo test --release --test reading --test reading_http
```

The generator reads typed Rust evidence and authored rule metadata. Exhaustive
enum matches and full struct destructuring make newly added fields/variants
an explicit regeneration obligation. Keep `rule_ids.json`: it preserves
stable rule identities independently of localized names. Do not maintain a
second rule list in the website or construct fake proof instances for metadata.

Source labels: optional `reading-titles.json` files beside actual sources own
Chinese/English example names. Capture validates and copies `sources[].titles`;
partitioning preserves these fields in manifests and chunks. The shared viewer
renders labels with text content and keeps the original path as identity.
The upload bridge admits only this additional presentation filename, includes
it in request cache identity and passes it through to child verification.

Builtin numeric hover cards in `web/reader.js` follow the scalar WD domains
in `execute_fact_stmt/well_defined_results/verify_obj/scalar.rs` and object
semantics in `ast/obj.rs`. They are language-reference documentation, not
expression inference. The 31 illustrative equalities were checked together
with strict release CLI verification (2026-10-24). Missing entries retain
generic help; resolved user symbols take precedence. With a checking host, all examples now open directly in the shared editable IDE
with grey inference buttons and resolved hover, using the same reading service. Changed text immediately clears old verification/evidence from
the view; rejected statements are marked red after checking. Pending draft coloring is lexical only; semantic hover and real inferred
FactIds return after checking. There is no separate reading/editing mode. Static
exports need a host checking callback or endpoint to enable editing. See
[Editing and checking](../../docs/reading.md#editing-and-checking) for the
callback, single-configuration project scope and local gallery proxy.

Optional host-authored `exampleGroups` add bilingual links to independent
reading bundles in the existing Examples menu. `includeSources: true` merges
the current chapters into the matching category without duplicates. The gallery
uses Passes / Does not pass categories. The shell reads them from an
optional JSON script `reading-example-groups`; only relative directory links
are rendered, and locale is propagated across navigation. This does not extend
the proof schema or merge failure bundles into a successful collection. See
`examples/reading/homepage/export_gallery.py` for the reproducible builder.
Items may provide language-specific `hrefs` alongside the existing `href`
fallback. The bilingual source lessons use these paths and standard same-origin
alternate-page metadata. The shell changes the authored source language only
when the original document is still open and `hasLocalEdits()` is false;
otherwise it preserves the source and changes the interface language. This
read-only component query includes checked edits that differ from the initial
text. No additional draft owner or per-example renderer is introduced.

`ReadingSite` writes optional source-only parts alongside the existing proof
chunks. Manifest `source_url` points to a `reading_source` envelope with the same
snapshot identity and a token-free source record. The shared loader validates
snapshot, source ID, path and text type, then caches only the text for
`getProjectSnapshot()`. Preparing input does not merge these parts into the
viewer or make unloaded proof available. Navigation retains its independent
full-chunk path. Older exports fall back to that path for source snapshots;
failed source loads retry and document changes invalidate pending snapshots.
This is an additive packaging capability, not a reading-proof schema change.

Upload checking uses a streaming JSON whitespace compactor between the child
CLI and the existing bounded output file. It preserves all string bytes and
field order, including the source and proof records. The unchanged 256-MiB
limit measures compact transport; the CLI's formatted JSON contract is unchanged.
Resource failures reap the worker and join its output collector before workspace
cleanup. This is transport handling, independent of capture, verification and
source-only loading. Pure streaming tests and real loopback/cache tests cover
the format and service boundaries.

The maintained `web/tests/host.cjs` acceptance runs the unmodified page shell
and reader against actual exported parts and actual strict CLI checks. It
covers a rejected predecessor, later unchecked chapters, restoration, keyboard
checking, and navigation while a result is pending. Working-copy edits clear
semantic selections immediately; rendering that draft does not cancel chapter
navigation. Restoring unchanged text is a no-op. The iframe bridge requires a
nonopaque parent origin and current bundle identity; disposed readers reject
new work. These component/CLI checks remain separate from browser layout
acceptance; see `web/tests/README.md`.

### Contextual explanations and reference cards

Predicate hover presents definition and proof together. Both use retained typed
data: the resolved declaration and complete predicate display, then the actual
verification record and its requirement/proof pairs. The builtin-rule and
strategy routes for intersection membership both expose the two member-set
proofs. Finite-set membership/non-membership explain the retained equality or
disequality certificates. Proof conditions expand on demand and must match
their evidence's fact identity; mismatched records remain unavailable.

Older bundles may attach accepted `by def`, `by thm` or `by contra` evidence only
to the execution result. The reader derives local display metadata from those
exact success variants, without modifying the bundle, allocating facts or
changing verification. Contradiction goals and local negation assumptions keep
their distinct roles. Current failed statements can show their definition and
check failure together. Unknown definitions and proof forms remain explicit.

The source occupies the full reading width. A contextual explanation opens
only after a source interaction, stays within the viewport and scrolls internally
when necessary. Close it with its close button, Escape or an outside click.
Changing examples closes it. The editor remains editable when inspecting help.
Pinned equality explanations stay at the selected relation operator. All
source cards dismiss when their owner leaves the editor's visible rectangle,
including horizontal scrolling; they do not remain detached from their source.

Authored builtin reference cards are shared by hover and click. Numeric cards
state input restrictions and results (for example `+` takes two complex numbers
and returns a complex number). Set operators such as `union`, `intersect`,
`set_minus`, `power_set` and family/indexed variants are explicitly labeled
**Set operator**. Their inputs are set-kind requirements, never a fabricated
universal set domain. Indexed union/intersection require nonempty indices in
the current verifier. These cards describe builtin contracts, not an inferred
type of the selected expression; resolved user declarations keep their own help.

Detailed keyword cards currently cover `prop`, `by def`, `forall`, `claim`,
`have fn`, `by contra`, `by thm` and `release thm`: summary, syntax, behavior/restrictions and a runnable
example. Other existing keyword hints remain concise. Numeric cards cover
arithmetic, real elementary/trigonometric/hyperbolic functions, integer
operations and complex parts/modulus; this is not exhaustive builtin coverage.
The format borrows summary-plus-detail from Python PEP 257 and the synopsis,
parameters/results and examples structure from Linux man-pages(7).

The `prop`, `by def` and `by thm` cards explain the shared `nonnegative(x R)` example
point by point. The expanded reference distinguishes formal parameter type,
predicate meaning, the complete defining equivalence, declaration versus
instance, and proof by substitution. Its equivalence is rendered with the
shared local math renderer, with complete text fallback. Hover retains the
compact reference and example, linking the reader to the full explanation by
clicking the source keyword. Detailed content scrolls inside the contextual explanation.

Theorem highlighting follows retained `TheoremCall` symbol references, not
name spelling. A retained resolved `Builtin` callee marks builtin theorem
identity; ordinary user theorems and mathematical objects remain distinct.
`release thm` has a shared hover/click reference explaining argument
instantiation, parameter-domain and premise verification, and publication of
all theorem conclusions. Its checked prime-divides-power example uses the
actual `(a, k, p)` parameter order. Builtin theorem cards currently give
mathematical statements for prime-divides-power and unique reduced fractions;
other builtin theorem names retain an honest category description.

Unique existence `exist!` is one highlighted/help span even when retained
lexical tokens split `exist` and `!`. The reader also accepts horizontal spacing
between these tokens, matching the parser. Its hint states existence and
uniqueness together; ordinary `exist` retains its existential hint and a
factorial `!` is not absorbed into a quantifier.

Builtin rule comments are produced by the owning proof type's
`rule_name_and_message_en` / `_zh` methods. Reading captures both languages on
**each actual rule application** as optional `comment.en` / `comment.zh`
`{name, message}` objects. This preserves different laws within one catalogue
family and supports language switching without rerunning a proof. The catalogue
remains the fallback for older exports. Adding a builtin family without a comment
owner fails the capture generator; a new variant must also satisfy the owner's
exhaustive Rust matches. New disjunction/existence comments currently cover
English and Chinese, with English fallback for other output languages.

Every retained successful atomic verification, including each adjacent equality,
ends with a closed **Well-defined expressions** disclosure. It reads only that
verification's WD certificate, retains its actual verified domain conditions and
proofs, and stops before walking into a condition's own proof. Each condition
opens its own explanation, with its own WD disclosure at the end. Closed numeric
conditions such as `2 != 0` remain inspectable. This presentation never changes
WD ownership, proof search, fact identities or verification order.
If atomic proof search fails after WD succeeds, the rejection explanation keeps
that same closed WD tail. A successful domain check never marks the goal proved;
a failure during WD continues to show its unmet condition as the diagnostic.

### Function interface and return evidence

Exact-interface cards distinguish stored membership from an anonymous function's
declared interface. They show the existing and required complete interfaces,
including guards and return domains; splitting shared parameter groups does not
change the mathematical interface. Call-return cards retain every participating
function property. Standard-return guarantees display their native numeric
inclusions; codomain proofs distinguish matching returns from alternative
interfaces with the same complete input domains at every call layer.

`AppliedFnSetReturnSignature` observes the existing return-set computation once:
it retains the application, ordered resolved interfaces and final return set.
It introduces no mathematical IDs, searches, argument proofs or stores. The
reader can show each actual parameter correspondence through an aliased returned
function space without implementing its own resolver. Expression checks remain
last and collapsed. Old exports use only structurally retained literal interfaces
and report missing alias-dependent substitutions honestly.

### Equality proofs at local source clauses

A checked local universal conclusion keeps its adjacent equality proofs at the
original equals signs, even when a later clause rejects the enclosing proof.
This includes theorem, strategy and claim closing checks that retain a proof
without creating a stored Fact row. The viewer follows the original quantified
goal, exact clause identity, local scope and adjacent endpoints; it does not
invent a stored fact or promote well-definedness mentions to source assertions.

Each equals sign opens its own proof, local context and direct citations.
Pinning, keyboard selection and following a scope or citation preserve the exact
equality on Back. Selecting the source line restores the whole clause; editing
invalidates the previous targets. The enclosing failed statement stays unfinished
and publishes no result. Definitions, unexecuted clauses and synthetic internal
laws do not acquire source equality proofs from this mapping. A partially failed
chain retains its own rejected-chain checks rather than becoming a completed
local clause.


### Rejected chain checks

A rejected source chain retains the checks of its adjacent relations. Each
actually verified equals sign opens that proof; the actual failed equals sign
opens its rejection instead. Later unchecked equals signs receive no proof
targets. A checked prefix is available in a closed disclosure at the failed
source row and header. Selecting a relation, pinning it or following its scope
and citations preserves its exact source position on Back. The original chain
remains unproved and publishes no result.

Mapping uses only the selected rejected source result: a direct fact, a retained
universal conclusion or a retained claim closing check. It does not scan arbitrary
nested WD certificates for a proof to attach. A universal may already have an
entered native scope and checked prefix when a later adjacent expression fails
WD; a claim whose goal fails WD has not entered its body. Predicate declarations
and unentered goal checks do not acquire asserted source results. Proof-search
failure and expression-formation failure keep distinct explanations. Successful
atomic checks and failed searches with a successful formation certificate keep
their own closed WD disclosure last. Missing or conflicting result/index/subject,
operator, endpoint or scope records cannot borrow another relation's proof.

## Whole-chain universal applications

When a retained universal proves an entire chain, the viewer shows that actual
application and its original conclusion, argument bindings, strict match proofs
and premises. Selecting an equals sign projects the corresponding adjacent
relation from the whole chain; it does not create an independent atomic proof
or a stored fact identity.

Native `VerifyChainFactSuccess.known_forall` now contains
`KnownForallChainProof { application, well_defined_proof }`. The latter is the
chain WD result already checked by the verifier, retained once in execution
order. Detailed output keeps the application fields and adds its
`well_defined_proof`; Normal output and mathematical storage are unchanged.
Older direct application payloads retain proof navigation and explicitly
report unavailable WD details in the final closed disclosure. Missing or
conflicting source, conclusion, binding or endpoint records do not acquire a
proof correspondence.

## Failed preimage and replacement constructions

Preimage and replacement constructions also have source-adjacent rejection
cards. The reader uses the exact retained execution dispatcher and failure
variant: source shape, unavailable function interface, preimage-name count,
unproved range membership, unavailable binary predicate, source formation or
missing replacement uniqueness. The count comes from the native result;
diagnostic strings are not parsed to recover parameters or declarations.
Range-membership and source-formation checks retain their actual subjects,
and the available formation evidence remains last and closed.

These older construction failures retain a stage rather than a complete
invocation history. The card explicitly reports that preceding checks,
substitutions and temporary properties were not retained. It invents no
definition links, proved prefixes, witness bindings or publication. Native
source byte spans and lexer tokens validate the command address; normalized
`source_text` is not assumed to reproduce the original source spelling.
Later construction/store failures, generated or repeated execution histories,
and the `Define` replacement failure still require separate source acceptance.

## Failed explicit definition checks

An entered `by def` failure retains its original statement, completed goal WD,
actual local failure and detached environment in `ExecByDefLocalFailure`.
Both user and builtin `DefinitionProofFailed::Requirement` payloads now retain
the instantiated requirement list and the actual successful prefix in order.
No requirement is reverified and no failed target is stored or published.

The source-adjacent failure card pairs these native requirements with their
proofs, shows the exact unmet condition and keeps later conditions explicitly
unchecked. Completed checks and the unchecked suffix start closed. The final
closed formation section keeps goal/condition WD separate from truth checking.
Definition and argument links come from the retained statement and resolved
declaration, not textual substitution. Old records lacking this context retain
their actual failed condition and explicitly report the missing history.
Goal-WD rejection does not claim that definition checking was entered.
Normal failure fields remain compatible; Detailed failure output additionally
includes `requirement_facts` and `proof_of_requirement_facts`.

Failed `by thm` and `release thm` calls retain their resolved callee and actual
instantiated requirements, completed verification/store pairs, detached local
scope and failed stage. The shared reader distinguishes preparation, argument,
complete-domain, premise and target-selection failures. Successful prefixes and
unchecked suffixes start folded; argument/formation checks are last. A selected
local theorem return is never presented as an outer proved fact when the whole
invocation fails. Copied theorem declarations carry actual parameter bindings,
so unopened source chapters need loading only when the reader follows the source
link. Legacy failures without retained history remain explicitly incomplete.
The focused source is
`examples/test_statements/negative/by_thm_stmt/retained-invocation-prefix.lit`;
producer tests are `tests/reading_failed_theorems.rs`, and interaction tests are
`web/tests/failed-theorem-invocations.cjs`. Retention of later derivation and
conclusion/closing WD failures is not full runnable-source or UI acceptance for
those paths. The full 52-statement reading audit remains unfinished.

A failed `by contra` retains its original source, successful goal formation,
actual reverse assumption and its verify/store record, completed body prefix,
exact failure and detached local environment. The reader keeps the temporary
assumption and actual consequences beside `?`, while the failed block has no
completed outer arrow. An earlier body failure marks the final contradiction
check as unexecuted. At `impossible`, the first successful proof remains
available even if construction or verification of its negation fails; the same
ordered closing evidence is used by case proofs. Argument/formation checks
remain last and folded. A genuine local hypothesis is hoverable despite its
owning block's failure; incomplete or foreign source/scope records cannot
create one. Old snapshots without the retained scope or first-side proof keep
explicitly incomplete histories. Complete final-store and assumption-formation
failure UI acceptance still requires runnable source probes.


Failed object introductions retain their actual ordered checks without
publishing a partial declaration. The source-adjacent explanation distinguishes
nonempty-domain checks, local typed parameters used only in type preflight,
value formation, instantiated value domains, and verified existential or
predicate sources before witness-count rejection. Completed checks and temporary
properties are collapsed; failed and unexecuted stages remain separate. A
failed declaration introduces no object or defining equality into its parent.
Older result snapshots that discarded these stages remain explicitly incomplete.
The dedicated tracer is
`examples/test_statements/negative/have_obj_equal_stmt/retained-membership-prefix.lit`.

Symbol hover and selection distinguish attempted declarations from completed
definitions. A rejected declaration keeps its source location and a link to its
actual checks, without presenting source equations, parameter domains or
defining conditions as established properties. Missing verdicts and ambiguous
execution records remain explicitly incomplete. The verdict belongs to the
declaration itself: a rejected use does not invalidate an earlier definition,
and an accepted declaration inside a later rejected proof remains a local
definition. Formal parameters retain their separate role. Repeated source
executions use the selected execution or its visible scope; they cannot borrow
another execution's definition checks. This is a read-only presentation rule;
it changes neither verification results nor symbol, fact or scope identities.


Failed predicate, struct and template definitions retain the original declaration
and the actual environment returned by each existing local-scope API. The
ordered failure variants keep parameter-type WD prefixes, conditions assumed
for later WD, earlier field declarations and the actual template body failure.
Struct field checks retain their nested environment separately from header
parameters. Successful result schemas, verification order and storage are
unchanged; Normal diagnostics keep their previous contract.

The source-adjacent card separates completed local checks, the failed input
and the unchecked suffix. Field and condition source rows distinguish checked,
failed and unexecuted stages. Local assumptions link to their actual FactIds
and scopes; they are not proofs of a predicate instance or public consequences
of a failed definition. Prefixes start closed and formation checks remain last
and closed. An unchecked source row has no formation proof of its own.

The public fixture generator's `--failed-interfaces` flag and
`web/tests/failed-interface-checks.cjs` exercise these selected histories.
Legacy, incomplete and foreign records cannot acquire reconstructed assumptions.
This is not exhaustive failure coverage: structure auto-opening, reserved
struct-header domain facts and additional template body variants still need
source-specific acceptance. The live parser currently supplies no struct-header
domain list; retaining that native branch does not establish runnable syntax.

## Quantified formation failures

Ordinary forall proof introduction and formation-only forall checks now retain
separate stage-ordered failure records and their existing detached local scopes.
Both keep actual completed parameter groups and premise assumptions. Formation
checking also keeps completed consequent WD certificates without treating those
consequents as assumptions or proved facts. For example, checking that `x = 0`
is a well-formed expression under `x > 0` does not prove `x = 0`.

The source-adjacent cards distinguish arbitrary parameters, adopted premises,
formation-checked clauses, the current failure and unchecked suffixes. Actual
local premise consequences remain collapsed and traceable by their native IDs;
failed universals publish no enclosing conclusion. A checked formation-only
clause has no fabricated proof/citation link. Selected earlier clauses use their
own WD certificate; unchecked clauses inherit no later certificate. Missing or
conflicting scopes, source identities, prefixes, endpoints and inference owners
remain incomplete. The parent scope is checked against the retained execution
record hierarchy, including nested definition scopes.

The runnable tracer is
`examples/stmt_nodes/definition/quantified_condition_formation.lit`.
The WD parameter helper's three peer consumers also retain their actual local
formation histories on failure. Existential-shaped bodies (`exist`, `exist!`,
`not exist`) are formation-checked and locally assumed in order for later body
checks. Negated universals and equivalences assume only common premises; their
consequents and equivalence sides have formation certificates, not proofs of
truth. No failed enclosing statement publishes those local assumptions.

Top-level negated universals are checked through an actual derived
counterexample existential; equivalences through two actual forall directions.
The reader follows the retained typed correspondence and exact child evidence,
preserving a completed first direction separately from a failed second one.
It does not equate distinct goal IDs by spelling or reconstruct missing proof
stages. Selected local inferences keep their true source and definition links
through lazy exports and Back. The public negative tracer is
`examples/test_statements/negative/def_prop_stmt/quantified-peer-formation-prefix.lit`;
producer checks are `tests/reading_peer_quantifier_formation.rs`, and public
events are in `web/tests/peer-quantifier-formation.cjs`.
Retained nonempty structural expansions also belong to these checking scopes.
Their actual membership stores, parameter checks, ordered objects and property
stores are validated before registering a source-local view. In formation-only
scopes the card explicitly describes the structural properties as temporary
conditions for checking expressions: they supply no existence witness or proof
of the original statement. Definition/field links and exact Back retain that
scope and its logical source location. Structural results start folded and add
no permanent source controls; their domain checks remain last and closed.

The current producer expands direct structure parameters during ordinary forall
formation/proof introduction. The peer existential, negated-universal and
equivalence formation helpers can legitimately retain
`auto_opened_struct_layers: None`; those records acquire no fabricated structural
properties. A null or incomplete expansion must be interpreted using its actual
pipeline owner, rather than assuming every parameter helper performed the same
stages. Multiple parameters, parameterized structures, false-but-formed clauses,
source/citation navigation and qualified lazy definitions have selected public
acceptance in `web/tests/formation-struct-openings.cjs`.

The earlier checkpoint exercised atomic/equality clauses; selected compound
clauses are described below. Actual structure-opening failures, later partial
openings and additional nested/generated/repeated histories still lack exhaustive
UI acceptance. The full statement-reading goal remains active.

## Compound quantified formation clauses

Source-adjacent formation histories cover selected conjunctions, comparison
chains and disjunctions. Complete clauses use their actual source/certificate
and store correspondence. A failed compound retains the ordered component,
adjacent-relation or branch prefix, current failure and unchecked suffix in a
closed disclosure. Earlier component checks establish only formation; they are
not assumptions inside the still-unaccepted compound. Disjunction formation is
not short-circuit evaluation and selects no true alternative.

In `exist x R st {x != 0 and 1 / x > 0}`, checking the first atomic expression
for formation does not adopt `x != 0` before the second check. The conjunction
therefore still rejects. With separate body clauses, the first completed clause
is locally adopted before later formation checks. Neither form provides an
existence witness simply by declaring the predicate. The public positive and
negative tracers are `examples/stmt_nodes/definition/compound_condition_formation.lit`
and `examples/test_statements/negative/def_prop_stmt/compound-formation-order.lit`.

Stored conjunction components and chain edges keep their actual indices and
identities; disjunction alternatives remain unassumed. A definition-derived
consequence of a stored conjunction follows the corresponding atomic inference
child and source component to its resolved definition. This uses retained typed
order, not substitution or rendered-name guesses. A failed quantified child
replaces a duplicate enclosing-definition card at that same source position only
when whole-fact identity and strict native scope ancestry agree; the definition
header still shows the enclosing failure. Source, Native records, proof policy,
store/check order and scope ownership remain unchanged.

## Ordinary compound failure histories

Ordinary conjunctions and comparison chains verify their atomic components in
order. Earlier successful checks are genuine proofs, while the failed component
and later unchecked components establish no whole conjunction or chain.
Disjunctions first require every alternative to be well-defined; a formed
alternative has not thereby been proved true. Thus `1 = 2 or 1 / 0 = 0 or 1 = 1`
stops during formation of the second alternative despite the true last one.

Source-adjacent bubbles preserve this distinction. Retained compound formation
prefixes, nested And/Chain alternatives and unchecked suffixes appear in a
closed disclosure inside the final formation section. Actual And/Chain proof
prefixes keep their own proof navigation. Failed adjacent equalities have their
own final, closed formation section, rather than displaying a failed domain
condition as a truth-proof premise. No successful formation certificate is
invented for a failed check.

The existing universal-failure and source-equality mappings identify selected
local conclusions and chain edges by their real owner, source, scope, subject
and component correspondence. This includes selected checks inside `forall`
and `claim`; an enclosing goal or neighboring equality cannot supply the
missing proof. Missing or foreign records retain an incomplete explanation.
Pre-entry goal failures introduce no assumption, and rejected statements publish
no outer conclusion or inference. See `web/tests/compound-fact-formation.cjs` and
`web/tests/failed-chain-proofs.cjs` for real Native/public-event acceptance.

## Failed explicit-assumption declarations

A failed `trust have` retains its actual parameter introduction, prepared body,
parameter-to-file-root bindings, completed body formation certificates, failed
index and unentered remainder. The statement transaction supplies its already
returned environment without changing discard/merge behavior. A direct template
body uses the template environment and introduces no extra scope. Optional
environments in generated capture enter a reading scope only when present.

Every body clause is checked for formation before any body clause is stored. A
completed body formation check is not yet an assumption, and supplies no proof
of its assertion. Closed source-adjacent folds distinguish that prefix, the
unestablished condition and unchecked clauses. Native bindings relate source
parameters to their actual prepared identities; the viewer does not infer that
relation from names or construct instantiated mathematics. Strict-policy failures
remain pre-entry and have no invented history. The current complete cards cover
atomic/equality body clauses and templates without additional template premises;
structure-opening and other compound histories remain qualified.

## Atomic formation failures and goal positions

The viewer distinguishes failed argument formation, predicate lookup/arity,
builtin predicate-domain requirements and truth search. Their authority is the
retained typed failure and its exact source subject, not a parsed diagnostic
string. Completed domain checks and failed requirements stay in the final,
initially closed formation section. Predicate signature failures report the
actual name and recorded expected/supplied argument counts. Analysis-domain
misses without a precise failed requirement remain incomplete.

Pre-entry goal failures use the retained goal's position, including question-mark
rows within nested `claim` and `by contra` blocks. The enclosing header provides
an overview and a link to that source row. Goal formation failure introduces no
assumption and publishes no fact. The shared viewer changes neither the Native
graph nor Normal output; source identity, scope, check order and publication
remain owned by execution. See `web/tests/atomic-fact-formation.cjs`.

## Reading a structural definition expansion

`release struct def` uses the checked membership and the actual one-layer
publication history. The source bubble groups field domains, this layer's
defining conditions and an optional coordinate representation. It displays
recorded structure arguments and links each matched field or law to its
defining source. The initially closed property list preserves direct store
order and FactIds; gray inferred consequences remain separately addressable.

Classification compares retained declaration and instance structure, using
resolved parameter and field identities, flattened field paths, coordinate
indices, instantiated types, laws and source positions. It does not construct
an instance or allocate an identity. Missing or inconsistent evidence retains
an unclassified property list. Lazy definition loading uses the existing
generation and connected-element guards. An actual proof may cite an earlier
automatic opening rather than a redundant explicit release; the viewer keeps
that actual citation. See `web/tests/struct-expansion.cjs`.

Actual scoped parameter introductions also retain automatic one-layer structure
openings. Their initially closed source hints and fact explanations connect
the local parameter membership to the structure definition and its recorded
field/law consequences. The logical source is the parameter introduction;
the original defining field or law is a separate link. Parameter membership
is an assumption in this scope, not an independently proved global fact.
Parameter-domain checks stay in the final closed formation disclosure.

Only retained entry contexts are eligible: quantified proofs, claim/theorem
bodies and the supported process frames. A failure after entry may retain
these local consequences without publishing an enclosing conclusion. A claim's
pre-entry goal check or an object's hypothetical type preflight must not become
an actual proof context; diagnostic phase alone does not establish entry.
Missing or inconsistent identities remain unclassified. Original TokenBlock
field order and typed binding identities locate field spans even when resolved
types acquire internal module qualifiers. Historical JSON without those spans
can still link to the whole definition. See
`web/tests/automatic-struct-origins.cjs`; partial/generated structure histories
and exhaustive result-branch coverage remain open.

## Origins of structural objects and temporary checks

Successful `have` and `have ... = ...` declarations connect their actual
stored structural membership to the recorded field domains and conditions.
`trust have` keeps its explicit object/body assumptions separate from these
structural consequences. Expanding the definition does not prove existence
of an explicitly assumed object. Property lists and coordinate representations
start closed; selecting a property links its real introduction and its defining
field or law separately.

A rejected trust-have can retain fully opened temporary structural properties
before body formation fails. The viewer presents them as checking context,
not publication to later statements. Earlier body clauses have only passed
formation; none become assumptions until every body clause passes. This also
applies inside a template's actual retained environment. A template parameter's
local structural condition and a temporary trusted object have distinct labels.
Compound clauses retain their original binders and actual file-root rewrite
bindings; display comparison constructs no AST or proof. Strict-policy rejection
and an invalid given object do not acquire successful introduction origins.
See `web/tests/struct-introduction-history.cjs`. Failed type preflight,
partial internal opening errors and exhaustive generated contexts remain
separate coverage boundaries.

## Executed strategy body statements

A successful strategy definition retains its checked proof body as ordered
source-statement references. Local object introductions, nested claims,
witnesses, existential elimination and explicit definition proofs keep their
own source spans, scopes and actual citations. Registering a strategy is
distinct from publishing its conditional conclusion as an unconditional fact.
The source observer only associates an already retained typed proof body;
it does not execute the strategy again or change verification.

See `examples/reading/strategy_body_steps.lit` and
`web/tests/strategy-source.cjs`. In that example, existential elimination uses
the recorded `RealLineComparisonWitness` certificate and local object
properties; proximity to a witness statement is not evidence of a citation.
Older exports without body references remain source-only at those positions.
Rejected strategies retain only the body steps actually executed. A completed
local step can have an accepted source record even when a later step or final
conclusion fails; the strategy itself remains unregistered. Its parameters,
adopted premises, completed body/conclusion prefixes and failing check are
retained in `ExecDefStrategyLocalFailure` with the already detached local
environment. The execution order and outer commit/rollback rules are unchanged.

The shared local-proof viewer distinguishes these checks from registration,
leaves checked conclusion lists closed, and follows actual local hypotheses
and definition sources. A failed final goal is identified from its retained
typed check and exact source, rather than a generic statement-kind message.
Missing or mismatched histories cannot supply assumptions or completed checks.
Legacy exports without those stages state the missing-history boundary.
See `web/tests/failed-strategy-context.cjs` and the strict negative tracer
`examples/test_statements/negative/def_strategy_stmt/retained-final-prefix.lit`.
Partial parameter introduction and every generated/repeated failure path still
require their own source and event acceptance.

Inference batches use the ownership scope of their actual stored conclusions,
settled after all environment snapshots have been indexed. A seed FactId may
occur both during temporary goal formation and in the actual proof; its preferred
fact-table scope cannot distinguish these occurrences. The retained typed
store/infer reference identifies the actual body event. Consumers must not pick
the first batch sharing a seed or source line, nor use temporary consequences
as proof-body results. This export annotation changes neither facts nor proofs.


## Rejected theorem-definition histories

Rejected theorem definitions retain their original local proof stages in
`ExecDefThmLocalFailure`: goal formation, arbitrary-parameter introduction,
adopted premises, executed body steps and the completed final-check prefix.
Universal and direct goals remain separate result routes. A later failure does
not register the theorem or publish its local helpers. Post-proof storage
failures retain the completed proof and already detached environment; this
retention does not establish source reachability for every such branch.

The source observer uses those original records for failed-goal hovers,
closed conclusion-check lists, actual local inference and definition/citation
navigation. Older exports without the local history remain explicitly
incomplete. A conjunction's `failed_component` locates the actual rejected
component; its checked prefix does not prove the whole conjunction. Generic
proof-search diagnostics are omitted when an exact typed local goal already
supplies the localized explanation; concrete condition errors remain visible.
Formation checks stay in the final closed disclosure.

See `examples/test_statements/negative/def_thm_stmt/retained-final-prefix.lit`,
`retained-compound-goal.lit`, `web/tests/failed-theorem-context.cjs`,
`tests/reading_failed_theorem_context.rs` and
`tests/failed_theorem_result_capture.rs`. Parameter-entry, operational and
every generated/repeated failure path need independent source acceptance;
retained fields alone are not a coverage certificate.

## Goals not reached during a local proof

After a claim, theorem or strategy stops in its body, the original goal can
show a compact `Not checked` annotation on its own source row. If final
conclusion checking stops at one item, later items have the same pending
status. The card shows the actual local context and links to the stopped
check; Back returns to that exact goal. A pending target is neither an
assumption nor a failed or successful proof, and supplies no inferred fact.

The reader requires the retained original goal, local scope, ordered source
body and complete executed prefix before classifying this status. Missing,
foreign and older incomplete histories remain unclassified. Contradiction
and case assumptions keep their own roles. The selected source acceptance
uses distinct goal rows; ambiguous shared-row and generated contexts need
their own evidence. See `web/tests/pending-goals.cjs` and
`examples/test_statements/negative/def_thm_stmt/pending-goal-after-body-failure.lit`.


## Rejected relation-law registrations

When a checked reflexivity, symmetry or transitivity law fails, its source card
shows the actual arbitrary parameters and adopted premises and states that the
property was not registered. The failed conclusion has its own source target,
local context and final closed formation checks. Local premise inference stays
beside the premise that produced it; those assumptions and consequences do not
become facts in the enclosing scope.

This view follows the exact registration-failure envelope and retained failed
universal verification. The law shape, predicate identity, source positions,
parameter stores, adopted premise identities, failed target and scope owner must
correspond. Shape/arity/pre-entry failures cannot borrow a later local context.
Missing or foreign records remain incomplete. Selecting an ordinary universal
premise also shows its own quantified parameter frame and other local premises,
while displaying the selected premise once. Case/contradiction assumptions keep
their existing parent-context behavior.

A registered property is distinct from its later use. The selected public
reflexivity/symmetry/transitivity caller sources actually verify by definition
or a stored universal; their success does not certify a KnownRewrite route.
The reader does not invent a specific registration-source citation that the
runtime did not retain. See `web/tests/registration-failures.cjs` and the strict
negative tracer `examples/test_statements/negative/register_transitive_prop_stmt/retained-law-context.lit`.

## Actual transitivity applications

An actual registered `Transitivity` or builtin `OrderTransitivity` proof pairs
the cited left relation with the separately checked residual relation, then
shows their shared endpoint and target. The residual expands through its own
retained proof: definition arguments and conditions, or exact calculation.
Definition conditions keep their citations inside the corresponding condition
instead of repeating a flat list of all descendant dependencies. Each proof's
own formation checks remain last and initially closed.

The reader validates the typed route, target identity, relation, all endpoints,
source ownership and scope visibility. A left relation may be a local premise,
an actual inferred consequence or a globally stored fact; following it preserves
that origin and Back returns to the exact application. A checked prefix inside
a failed theorem remains local. Incomplete or foreign records never acquire a
constructed derivation. The retained runtime has no selected registration-source
FactId, so the card does not invent that citation.

See `web/tests/transitivity-applications.cjs` and
`examples/proof_nodes/atomic/by_known_rewrite/registered_transitivity_application.lit`.
The qualified acceptance registers the relation in the caller chapter. An
earlier-file-only registration and a mixed strict/non-strict order probe
currently have bare search misses; their source evidence is preserved in the
local reading todo. These observations neither change search permissions nor
certify reflexivity/symmetry applications or all transitivity combinations.

## Proof-command source addresses

An accepted proof command has a source execution address even when its returned
fact cannot own that header row. A block-form `by def:` retains its checked goal
at the `?` row; the command header now exposes that same actual definition proof.
A bare `release thm` can return a theorem's existing FactId, including across
source files, without publishing any new FactId. Its header exposes this actual
application while the canonical fact keeps its original producer and source.

The shared logical-action index derives this address from the accepted typed
execution, verified source token span, local scope owner and exact returned
store/subject identities. It uses the existing proof and theorem renderers.
No new source row or inline button is added. Pinning preserves the command
address; following a definition or original conclusion and returning restores
that exact invocation. Missing or foreign histories cannot create the address.
See `web/tests/proof-invocation-addresses.cjs` and the existing canonical
`examples/test_statements/by_def_stmt.lit` and `release_thm_stmt.lit`.

## Definition proofs keep citations within their obligations

User and builtin definitions display their retained obligation/proof pairs.
Each obligation owns its proof citations; the parent does not flatten nested
quantifier parameters, local consequences or later stored facts into a root
Context list. For `by def {1} $subset {1, 2}`, the initial card shows the complete
universal membership condition. Expanding it retains the arbitrary element,
its actual equality from singleton membership, the builtin membership rule and
links back to the local origin. Native scope and fact storage are unchanged.

Ordinary nondefinition builtin/strategy rules retain their actual root inputs
and rule identities. Missing definition requirements/proofs receive an honest
incomplete-history note; conflicting pairs do not acquire a derivation. Each
proof's own formation checks remain last and initially closed. See
`web/tests/definition-scopes.cjs`.

## A theorem call with several conclusions

The source header of `release thm release_sides(4)` explains the actual call
once: its resolved theorem, argument substitution and checked premises precede
the complete list of returned conclusions. Each conclusion links to its own
FactId and canonical producer. Pinning, following that link and returning
restores the exact invoking statement, including repeated and qualified calls.
Later use of a conclusion retains its own proof route.

One final, initially closed formation disclosure separates the call's shared
argument/domain checks from each returned expression's own certificate. A
missing or mismatched certificate remains incomplete for that conclusion;
it cannot borrow the next conclusion's checks. Inferred consequences are not
counted as additional theorem returns. See `web/tests/theorem-conclusion-groups.cjs`.

## Instantiating a universal equality in reverse

The actual `ByKnownForallFactViaSymmetry` route shows its cited universal,
recorded argument correspondence and premises, the retained reversed equality,
and the symmetry step that obtains the source goal. For an assumed
`forall x R: f(x) = x`, the reader shows `x = a`, then `f(a) = a`, then
`a = f(a)`. The intermediate equality is not presented as a stored fact.
Each equality in a chain keeps its own proof and exact citation/Back address.
Missing or foreign records cannot supply the derivation. The shared argument
correspondence check also serves whole-chain universal applications.

The maintained tracer is
`examples/proof_nodes/equal/by_known_forall/instantiation_then_symmetry.lit`;
the public-event checks are in `web/tests/forall-equality-symmetry.cjs`.
This is equality symmetry after a universal application, distinct from a
registered predicate's symmetry property. Registration examples whose actual
proof uses definition unfolding remain displayed by that route.

## Coordinate consequences of a tuple equality

For `have p cart(R, R) = (1, 2)`, the existing native inference publishes
`p(1) = 1` and `p(2) = 2`. The viewer explains each actual stored result
separately: the original equality, the `TupleCoordinates` rule, tuple length
and selected one-based coordinate. The gray source annotation stays closed
until requested. Later arithmetic can cite these actual coordinate FactIds;
following a citation and returning preserves the exact source address.

The observer checks the retained source identity, orientation, ordered stores,
subject/index/value pairing, scope and source positions. Reversed and conjunct
seeds retain their own origins. Nested tuples open one direct layer per seed;
an alias or empty tuple does not invent coordinate consequences. Local results
inside a rejected proof remain local. Incomplete or conflicting histories
receive an incomplete explanation rather than another coordinate's evidence.

A qualified `release obj def points::point` retains the original declaration's
source position while publishing its new stores at the release command. The
reader checks this correspondence against the actual defining declaration,
loads its source on selection when needed, and preserves both navigation
addresses. Retained private parameter names in ordinary typed-object
declarations are paired with exported names only through that same source
declaration, parameter positions, domains and recorded values. Other unresolved
or partial declaration forms remain incomplete.

See `examples/infer/equal/tuple_coordinates.lit` and
`web/tests/tuple-coordinate-inferences.cjs`. These source-event tests include
actual native exports, a lazy two-source book and missing/foreign-record
controls. They do not certify every generated inference branch or browser
geometry.

## Numeric equality substitution and its remaining proof

For `have p cart(R, R) = (1, 2)` followed by `p(1) + p(2) = 3`,
the retained `ClosedNumericEqualSubstitution` result identifies the cited
coordinate equalities, the rewritten equality `(1 + 2) = 3`, and its checked
residual proof. The source bubble shows these three stages using those actual
records. A premise already present in the local context is marked as used
rather than repeated. Each chain equality keeps its own certificate, citations
and return address; the residual is inspectable without becoming a stored fact.

The observer checks the exact target, retained operands, residual proof,
source positions, scopes and cited stores. It does not run a second rewriter
or invent a subterm-by-subterm substitution path that the producer does not
export. Closed numeric representatives may themselves be expressions such as
`min(1, 2)`; the display preserves them instead of replacing them with an
unrecorded numeral. Ordinary calculation, congruence, definition and theorem
routes keep their own explanations. Missing or conflicting records remain
incomplete. Both the outer fact and an expanded residual keep their own WD
checks last and initially closed. See `web/tests/numeric-rewrites.cjs` for
source, symbol, keyboard, operator, citation, edit and lazy-export checks.

## Unexecuted enumeration bodies

A successful enumeration can establish `forall x {}: 0 = x = 1` without
executing its proof body. Source-only body rows now explain why they were not
executed and link to the actual enumeration goal, execution history and final
closed WD. They do not acquire proof, WD, hypothesis, inference or stored-fact
records of their own. Empty parameter combinations and nonempty enumerations
whose every assignment has a premise proved false have distinct explanations.

The observer requires the retained successful parent result, goal/store/WD,
exact source ancestry and token ranges, and genuinely unavailable child
execution. Nested source clauses and repeated empty executions retain their
actual source addresses and separate parent links. A checked local enumeration
inside a rejected theorem remains local. An executed source instance,
incomplete history, failed parent or mismatched scope/source cannot supply the
nonexecution explanation. No extra inline or toolbar button is added; source
hover, line-number focus and selection use the existing contextual bubble.
See `web/tests/unexecuted-loops.cjs`, including the four original Mechanics
rows under empty enumerations. This does not classify every reason that an
arbitrary statement lacks execution evidence.

## Large proof graphs keep complete source explanations

Evidence indexing uses an explicit worklist. A probability chapter can retain
more than 150,000 evidence nodes; passing that entire array as arguments to
`push` exceeded JavaScript's call-argument limit. Indexing then stopped before
the universal-source index was complete, causing later chapters to report
missing parameter correspondence even though their Native records were present.

The shared walker now pushes children individually in reverse order, preserving
the original depth-first visitation, callbacks and reference deduplication.
There is no proof truncation, node cap, alternate parameter matcher or relaxed
missing-data guard. The actual probability-to-orthogonal-projection path retains
the universal's three arguments, alias equalities, proof citations, exact Back
and final closed WD. First-open, full Native and lazy source-menu paths use the
same observer. See `web/tests/large-proof-graphs.cjs`; its 52-kind checks are
compatibility smoke checks, not exhaustive statement-result validation.


### Atomic facts rewritten using established equalities

The source proof bubble now explains retained non-equality atomic
`ClosedNumericEqualSubstitution` and `KnownEqualObjSubstitution` results. For
`let let_s = {1, 2}; 1 $in let_s`, it identifies the actual equality used,
the native rule, the retained `1 $in {1, 2}` obligation and that obligation's
expandable proof. Numeric order facts use the same display owner as numeric
equality rewrites. No term substitution or replacement positions are computed
by the viewer. Original target, rewritten result, proof, owner, scope and
citation identities must correspond; missing or foreign records remain
incomplete. The residual is not published. Each proof keeps final closed WD.
Cited equalities select their exact retained FactId, including adjacent facts
whose source statement is an equality chain. A retained generated local check
without its own source address is explained through its actual owner and scope;
no source location is manufactured.
This adapter covers these two captured atomic rewrite variants; function-unfold
substitution, order-dual and registered-law applications are separate routes.

### Function unfolding and converse relations in atomic proofs

Retained `FnApplicationUnfoldSubstitution` results show each checked expansion
equality and the resulting atomic proposition with its own proof. For
`6 $in multiples(3)`, the actual claim closes by expanding
`multiples(3) = {x Z: $is_multiple(3, x)}` and reusing the established
set-builder membership. Opening the equality shows the actual definition and
`m = 3`; the reader does not substitute into source strings. Multiple changed
function arguments require their individually corresponding equality proofs.

`OrderDual` shows the recorded converse relation, its rule name and the proof
of that alternate goal. For example, a checked `not a < b` may establish
`not b > a`. Positive strict/weak examples can use different native routes;
their source spelling alone never supplies an `OrderDual` explanation. The
adapter recognizes only the producer's twelve strict/weak order and proper-set
converse pairs, including their negations, with exactly exchanged operands.
It does not infer plain subset converses or symmetry of arbitrary predicates.

Both routes use the existing source-local proof controls and final closed WD.
Claim closing targets and contradiction-closing checks retain their actual
local scopes; alternate goals and expansion equalities are proof obligations,
not additional published facts. A claim's declared goal must correspond to its
recorded exported store before its closing proof is opened. Missing or
conflicting evidence cannot supply a successful derivation. These observer
adapters do not change verification, storage, inference, source or FactIds.

### Function bodies within equalities

Equality `FnApplicationUnfoldSubstitution` results use the same builtin-rewrite
display owner. For the Newton example, the first equality of
`newton(x) - r = (x^2 - 2*x*r + 2)/(2*x) = (x-r)^2/(2*x)` shows the actual
function-application expansion, parameter binding and checked residual
equality. The second equality keeps its own proof. Projection and plane-addition
examples retain the same operator-specific navigation, including tuple results.

Each captured expansion has an initially closed source/binding disclosure;
the residual has its own proof and final closed WD. Multiple occurrences and
both sides retain the producer's order and exact arguments. The reader does
not rewrite a scalar tree, expand inserted bodies, construct a proof wrapper
or choose a same-named declaration. Function-body equalities supplied by local
premises or aliases link to those actual sources. A selected body's narrower
carrier and guard checks join the outer fact's final WD disclosure.

Some theorem-goal clauses and chain steps have no separately stored fact. Their
retained execution, original source clause, local scope and exact operator own
the explanation; citation and Back preserve that source address. Their expansion
and residual certificates are not published as additional facts. Missing or
conflicting target, source, application, binding, WD or residual records remain
incomplete. Existing definition normalization reuses the same anonymous-body
source renderer; it keeps its own proof route and unfolding order.


## Failed witness checks keep their actual stage

A rejected `witness` is explained by its retained native dispatcher and failure
variant. `witness exist x R st {x = 2} from 1` stops at the substituted condition
`1 = 2`; a wrong carrier, an unproved membership and an unproved uniqueness
condition have separate explanations. A substituted expression's formation
failure is not relabeled as a failure to introduce or open its parameters.
Predicate arguments, witness expressions and set expressions retain their own
checks. Existential-statement formation reuses the quantified formation view,
including its actual temporary scope. A diagnostic phase can describe a deeper
requirement; it does not select the witness stage.

For a failed local proof body, the native `prior_steps` and failed child supply
a closed list of accepted local statements and an exact link to the stopping
source statement. Each link returns to the invoking source address. A failed
witness publishes no new outer conclusion. The failure result does not retain
the complete earlier ambient, binder, substitution or obligation history; the
reader explicitly leaves that history incomplete. Missing or foreign source,
result, scope, child or prefix records cannot supply invented explanations.
The current failure's retained expression checks remain final and closed.
These selected source cases do not certify all internal witness failure paths,
ordinary-source AutoOpen failures or browser geometry.


## Uniqueness checks have their own candidate scope

`witness exist! x {0, 1} st {x = x} from 0` supplies a concrete witness but
does not establish uniqueness. Its rejected uniqueness check retains two
arbitrary candidates, their declared domains and assumed conditions, and the
equality that remains unproved. The source-adjacent card shows this actual
local context, rather than treating those candidates as the supplied witness
or as additional source statements. Conditions and structural properties start
closed. References retain their actual FactIds and return to the invoking
witness; nested claims and theorem parameters keep their own scopes.

The shared universal-failure validator checks parameter stores, assumptions,
completed goals and the failed target. The uniqueness consumer additionally
checks that the one target equates the two recorded candidate tuples in order.
The existing scope indexer can keep generated contexts hidden from the source
while retaining navigable local conditions. Candidate-domain WD stays in the
final closed disclosure. A cached WD reference whose target is absent is now
marked unavailable by the shared renderer; a same-spelled object or another
scope's registration cannot replace it. This does not recover the discarded
earlier witness history or certify all internal/generated result branches.

Successful local uniqueness proofs use the same scoped parameter, assumption
and conclusion validator. Their candidate scope is a child of the retained
witness environment, not the statement's outer environment. Following a
candidate condition shows its arbitrary parameters and inherited context;
structural candidates retain their actual automatically opened properties.
Generated scopes add no source rows or permanent source controls.

One witness row may execute repeatedly:

```litex
by for:
    ? forall n range(0, 2) => n = n
    witness exist! x {n} st {x = n} from n
```

The existing execution picker selects `n = 0` or `n = 1`. Each choice retains
its own candidate premises, proof, assignment citations and Back destination.
The native store can reuse the source existential's FactId across executions;
the reader preserves that fact's original ownership and addresses the selected
invocation through its actual execution record. It does not manufacture a
second FactId or replace the later execution with the earlier proof. Missing
or conflicting owner, scope, store and conclusion records remain unavailable.
These checks cover the retained successful local-introduction route; they do
not certify all generated or cross-file uniqueness histories.

A selected two-source qualified export is also covered by
`web/tests/qualified-uniqueness.cjs`. It follows structural candidate properties
to their actual field definitions, loads an unopened defining source, and
returns to the exact invoking execution. In that export, the repeated concrete
witness checks reuse an earlier uniqueness universal: the reader shows the
cited proposition and recorded bound-variable correspondence, without claiming
new local candidate assumptions. Editing or destroying the reader while a
definition is loading cannot restore old proof contents; missing or foreign
definition chunks are not adopted. The shared app additionally preserves the
definition file and configuration when editing and rechecking the proof file.
These are verification gates for the existing reader, not a new proof route.

The same test records an unresolved qualified-object boundary. A named
structural object exported from the defining file can fail membership checking
in the application file even though the corresponding REPL probes pass. An
explicit membership statement in that file also fails; it is not a verified
repair. The successful cross-file tracer uses the literal tuple as witness.
Both real rejected projects remain negative controls with their actual failure
stage; no witness or uniqueness proof is reconstructed for them. This observer
work does not repair or assign a definitive cause to that verifier difference.

## Repeated witness proofs and scoped source references

```litex
prop reading_has_copy(a R):
    exist x R st {x = a}
by for:
    ? forall n range(0, 2) => n = n
    witness $reading_has_copy(n) from n
    $reading_has_copy(n)
```

Each witness invocation uses its actual execution record, even when its
returned source FactId is shared with an earlier invocation. Existential,
predicate and nonempty-set witnesses share the same dispatch/source/scope/
return correspondence check. Nonempty-set membership also corresponds to the
recorded witness and set. Missing or conflicting execution records produce an
incomplete explanation, rather than borrowing a neighboring proof.

A proof reference carries its consumer's retained scope. When the cited
FactId has several checked source executions, the reader selects the unique
nearest execution in that scope chain, using the actual checked/store pair or
witness return at the same canonical source statement. This handles both a
nonempty witness citing its local proof-body membership and a later fact or
inferred consequence citing the current predicate witness. The selected view
keeps the real FactId and actual execution statement; it does not rewrite the
Native fact's projected owner. Ambiguous or missing correspondences keep the
original Native address. Direct `selectFact(id)` retains its existing default
address; contextual source references do not change that public API.

These are transient source views over retained results, not new proofs or
facts. Source rows and the existing control layout stay the same. Binding conditions,
assignment references, inference origins and Back retain the selected
execution; expression checks remain final and initially closed. This resolver
covers the demonstrated primary checked/store and witness-return sources. It
does not establish complete addressing for every generated component,
inference, cached-WD certificate or discarded history.

The have-object source also has an explicit registered-file boundary: it passes
as an unregistered file, but the same source under an `f0` export rejects the
later equalities at lines 9 and 16 in the frozen producer. The old and new
reader executables return identical proof data for both modes apart from
executable/bundle identity. The registered replay checks the three successful
existence introductions and the actual later failures; it does not claim that
the intended mathematics passed. The producer boundary remains unresolved.

For source-authored `have ...:` conditions, the reader separately observes
whether each object identifier has a retained declaration correspondence.
It uses exact declaration identities, source definition occurrences, explicit
builtin identities and parameter groups retained inside the condition. A
same-spelled name or a parameter appearing in an unrelated proof is not a
correspondence. Constants and conditions about previously declared objects
remain valid display cases; a condition need not mention the newly chosen
object.

Conditions with missing correspondence remain accessible in a qualified
disclosure, rather than appearing as ordinary properties of the declared
object. Object hover includes this disclosure even when the unmatched condition
uses a different identifier. Fact citations, including inference sources, keep
the qualification and their actual FactIds. Selecting a condition opens its
disclosure; Back retains the original selection. This is a reading-data
qualification, not a change to verification, storage, namespace resolution or
the public fact-selection address.

The observed `AlgorithmEquation` / `FailToSearchProof` route now shows the exact
failed equality retained in that command's typed result. This is an
unsuccessful proof target, not a published result. An exact resolved algorithm
identity can link to its accepted definition. If an outer computation fails
while checking an inner algorithm, the bubble shows that inner equality,
rather than inventing an equality for the outer source expression. Expression
formation remains last and initially closed.

A predicate-conditioned case split supplies a real example: evaluating a
nonnegative flag at3 reaches a retained `reading_predicated(3) = 1` certification failure;
explicitly proving its predicate condition before evaluating supplies the
actual fact cited by the successful equation proof. The viewer does not infer
the missing search history or select a source branch from the return value.
The separate `FailToVerifyWellDefined` payload now has an actual source
control: an algorithm whose argument belongs to a named singleton is called
at0.5. Numeric normalization produces1/2, whose membership the current checker
does not establish until the original membership is explicitly recorded.
The bubble shows the retained normalized defining equality and identifies
formation as the stopping stage; equality search was not entered. Its failed
domain condition remains in the final closed disclosure. The valid eval
envelope owns this internal equality's checks, rather than requiring that
generated equality to have a standalone source-fact address. No source
position, normalization equality or missing computation history is invented.
Ordinary/registered, partial, inner-call and claim controls keep the actual
definition and citation identities. This display change does not repair the
verifier's composition of membership evidence across normalization.
CyclicAlgoCall and EvaluatedEqualityWellDefined still have no positive source
coverage in this audit; rejected self-reference and a recursion-depth limit
must not be presented as those different stages.
