# Finite probability concepts and dependency boundaries

Finite probability is a structure on an actual sample carrier and all its
subsets. A package with Ambient set plus carrier power_set(Ambient) keeps this
carrier explicit without claiming a set of all sets. FiniteProbabilitySpace
owns finite/nonempty, normalization, nonnegative and binary disjoint-additive
invariants. Two scalar weights are a useful example, not its general model.

The probability function is data. Event relations are facts; native union,
intersect and set_minus remain the event constructions. The forward proof
spine is the actual disjoint split A=(A intersect B) union (A minus B), then
finite additivity, complement/difference, monotonicity, probability bounds and
inclusion-exclusion. Set extensionality proves both directions and a
contradiction proves disjointness. The 79 exported source theorems are checked;
the source adds no strategies or reserved native theorem names. The kernel
provides four bounded power-set closure cases.

Conditioning is a function family indexed by Ambient and a supplied space:
\conditional_event_probability<Ambient,space>(A,B). The ordinary arguments
are events and P(B)>0 belongs in the domain. A scalar joint/evidence quotient
alone would lose those event/space contracts. Product and Bayes are arithmetic
consequences; Bayes needs P(A)>0 as well as P(B)>0. Independence is a prop with
four arguments and equality P(A intersect B)=P(A)P(B); quotient-based
independence would silently discard null cases. Symmetry and the two guarded
conditional equivalences are delivered.

Uniform probability is the actual function family
\uniform_event_probability<Omega>(E): R, for nonempty finite Omega and
E power_set(Omega). Native cardinality supplies its values, denominator
positivity and finite union identity. The three formula laws are independently
exported and generic, not numerical tests. No new counting function or
unjustified integrality premise is introduced.

Delivered source is91 top-level statements: one structure, one predicate,
eight templates (six function families and two bundled values),79 theorems and
two internal universal facts. The event and
numeric closure exports let independent generic callers state the same
compound goals without adding premises or strategies. They supply typing
facts, not probability assumptions or theorem certificates.

The generic uniform model is now constructed as
\uniform_probability_space<Omega> = (Omega,\uniform_event_probability<Omega>).
Its finite/nonempty domain is unchanged. uniform_probability_laws/1 reuses the
three formula laws and proves full FiniteProbabilitySpace membership. The
bounded TemplateApplicationInStandardSuperset leaf closes intrinsic real
call outputs in C with exact declaration/alias/stored-signature evidence;
argument guards and search permissions are unchanged. Imported callers check
the same generic contracts, and the actual six-outcome bundled dice yields
conditional probability2/3. A tuple definition is explicitly published before
field projections in the registered caller; a REPL-only deletion probe did
not justify removing that step from the registered file.

The Dirac model is now constructed on any finite Omega with a supplied
point in Omega. Its actual function is
\dirac_event_probability<Omega,point>(E) = finite_set_size(intersect(E,{point})).
The contains/excludes laws prove values1/0, and dirac_probability_laws/2
packages normalization, nonnegative values and disjoint additivity. A witness
using the supplied point proves nonemptiness. The new one-operand intersection
strategies solve the exact former declaration-WD gap while retaining existing
child permissions and the old both-finite evidence. Their independent native
tracer and generated3-theorem Lean pair check both sides and cardinality WD.

The actual point mass at1 on {0,1} has the nonempty null event {0}. The public
caller proves P({0})=0, P({1})=1, their independence and P({0}|{1})=0; conditioning
on {0} refuses the actual positive-evidence guard. Independent imported contracts
retain all generic Dirac domains. Outside points/events and empty/infinite
Dirac carriers are rejected.

The positive complement guard now verifies through the independent bounded
SetMinusInPowerSetOfLeft carrier-equality rule. total_probability_two_events/4
reuses the disjoint partition and conditional product laws, with an explicit
extensional proof that A intersect (carrier minus B) equals A minus B. It
keeps both branch probabilities positive; no independence is required. The
actual dice example proves both branch conditional values2/3 and1/3 and total1/2.

Source-only additions are null_event_independent/4, independence_complement_right/4,
independence_complements/4 and conditional_event_monotone/5 (comparison A,B,
conditioning event E). They reuse existing laws with exactly their zero,
independence, inclusion and positive-evidence premises.

The generated Lean pairs cover one-bound finite intersections and complement
event typing, not the full probability structures. Complete probability Lean
compilation remains future work.

Downstream work remains correlation, distributions and statistical inference. Countable and measure
probability need their own concepts and are not implied by a finite carrier.

Finite real observables are actual functions on the supplied sample carrier.
finite_expectation<Ambient,space>(X) is the actual weighted finite-set sum of
X(k)*space.prob({k}); singleton domains use the general bounded
ListSetInPowerSetFromMembers rule with exact member evidence. No new native
Obj, reserved BT, carrier premise or search permission is introduced.

The source exports formula, pointwise extensionality, positivity, monotonicity,
vanishing, zero, constant and interval bounds. The additional singleton-weight
formula is proved by finite-cardinality induction using a local induction
proposition. Its step removes one actual event member and reuses binary disjoint
additivity and the native disjoint finite-sum partition. Constant expectation
uses that normalization and the existing complex scalar-sum theorem, with
checked real/complex function substitutions; it does not assume atom masses sum1.

The maintained caller computes actual dice expectation7/2 and point mass
expectation1. A real observable with values100 at the null outcome0 and1 at the
mass point still has expectation1. Forty-four negative controls include missing
pointwise hypotheses, wrong output/input domain, binary or partial samplers and
an incorrect mean. Numeric literal expansion publishes each actual point
membership and atom value before the bounded sum consumer reads them.

Proof-authoring gaps remain recorded: nested anonymous-function beta under a
product and anonymous real-sum scalar substitution did not automatically close
the attempted chains. The accepted route first proves the statement for an
ordinary supplied function, then instantiates the literal function; scalar
normalization keeps the named complex-valued weight until its final value.
No kernel change or false mathematical negative was inferred from these misses.

The source now constructs finite_variance<Ambient,space>(X) as the actual
finite expectation of the centered square. Its exact total-real domain matches
finite_expectation. Linearity is proved from ordinary weighted functions and
existing complex finite-sum addition/scaling, with checked real/complex pointwise
substitution; the public interface builds the anonymous linear combination
itself. A supplied-function linear-combination helper retains its actual
pointwise relation rather than assuming an expectation equation.

Add/scale/subtract/affine, variance nonnegative/constant/second-moment and the
square-expectation bound are source theorems. Small local scalar lemmas instantiate
checked equality/order transport at compound expectation objects where the
bounded congruence attempt did not close; no proof permission changed. All
rejected steps remain in persistent journals. Independent imported contracts61
and actual caller155 target this checkpoint, with52 refusal controls.
Dice E(X²)=91/6 and variance35/12; Dirac identity variance0 preserves differing
null/mass-point values. Full probability Lean and release checks remain separate.

Affine variance is proved by the supplied-function relation Y(k)=aX(k)+c,
its derived mean, pointwise centered-square scaling, existing expectation
linearity and checked scalar transport. The public interface constructs the
actual affine sampler; a=0 and negative a remain legal. Coefficient0 does not
legalize an undefined input function. Scale and translate are wrappers of the
same fixed contract, with no positivity/nonzero assumption.

finite_covariance<Ambient,space>(X,Y) is the actual centered-product expectation
of two total real samplers. Its formula, symmetry and self=variance source
laws use pointwise beta/commutativity/square identities plus the existing
expectation extensionality theorem. There are no native/Rust/Core/state or
permission changes in this slice. Source77/65thms/eight templates;
independent contracts68 and caller172 are the strict file-gate targets.
At that earlier checkpoint, covariance product-moment/bilinearity remained open;
those laws are now delivered below. Correlation and random-variable
independence/distributions remain later work; no zero-covariance independence
converse is claimed. The prior matrix compiler failure is resolved by the
focused refresh and separately reused phase6v1294-pass evidence.

The final constant covariance slice adds finite_covariance_of_constant_left/5
with an actual supplied function and pointwise X(k)=c, then constructs literal
constant-left/right samplers in the two4-argument interfaces. It derives E(X)=c,
proves the centered product vanishes pointwise and reuses expectation vanishing
and covariance symmetry. There is no constant certificate or new primitive.
At that earlier checkpoint, source80/68thms/eight templates, contracts71,
caller178 and63 refusal controls were the final gate targets. Zero and negative constants remain valid, while missing
pointwise relation and nonreal constants reject their exact theorem obligations.

Covariance product moments follow by expanding (X-EX)(Y-EY), applying the
already proved expectation linearity to its product/linear/constant terms, and
normalizing the scalar result. The public value and sampler contracts are
unchanged. Named-function helpers preserve the supplied pointwise relation;
constructing a literal combination is a separate convenience interface.

Left bilinearity follows by centering a supplied H=aX+bY and distributing its
product with the centered third observable. Right bilinearity uses symmetry.
Applying both sides to Cov(H,H), then self=variance and symmetry, gives
Var(aX+bY)=a²Var(X)+2abCov(X,Y)+b²Var(Y). In particular a covariance-zero
premise is required to remove the cross term. Event independence is a different
relation and is not silently used to stand in for random-variable independence.
The two-sided affine law also uses the existing constant-covariance theorem.

These eleven additional source theorems require no new value, prop, builtin,
strategy, trust or state. The resulting source has91 top-level statements and
79 named theorems. No nonzero/positive coefficient premise is introduced;
zero coefficients still require actual total real input functions. Generic
import contracts and the correlated dice observable Y=2X+1 exercise the same
interfaces. Measure probability, distributions, correlation and full probability
Lean replay remain separate work.
