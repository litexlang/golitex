# Math Concepts in Litex Scratch

This directory is a planning and executable-scratch workspace for six small,
independent Litex projects. Each project now has a checked first version. It is
not a textbook or part of `std`, and the later gates in each `plan.md` remain
design rather than implemented API.

Each child project owns:

- `plan.md`: scope, mathematical spine, examples, stop line, and acceptance
  gates;
- `main.lit`: the current executable first-version spine;
- `litex.config`: a standalone module exporting only `main.lit`;
- `README.md`: factual status of the current executable artifact; and
- `math_collections.md`: the ideal concept and interface design.

The projects intentionally do not import one another yet. The arrows below are
mathematical dependencies and reader order, not hidden runtime dependencies:

```text
elementary algebra and inequalities
            |
            v
sets, functions, and relations
       /             \
      v               v
number theory     Euclidean geometry
       \             /
        v           v
  linear algebra core    single-variable calculus
```

The graph is not a claim that number theory or geometry logically requires all
earlier files. It records the intended learning path: calculations first,
shared mathematical language second, two contrasting domain worlds third, then
an abstract algebraic structure and a staged approximation-based theory. The
last two projects are parallel destinations rather than dependencies of one
another.

## Six roles

| Project | Reader promise | Starter tracer | Intended flagship | Stop line |
| --- | --- | --- | --- | --- |
| `elementary_algebra_and_inequalities` | Recognizable school mathematics becomes checked calculation | Two-variable AM-GM | A radical equation with domain and extraneous-root control | Before trigonometry, probability, or calculus |
| `sets_functions_and_relations` | Objects, relations, and constructions get usable interfaces | A concrete preimage | Two-sided inverse iff bijective | Before ZF foundations, cardinal arithmetic, quotients, or choice |
| `number_theory` | Witnesses, induction, and discrete structure form a natural proof chain | Divisibility transitivity | Linear Diophantine solvability through Bezout | Before unique factorization machinery, reciprocity, or analytic number theory |
| `euclidean_geometry` | A visual domain grows from readable definitions and checked facts | The 3-4-5 distance computation | Euclid I.1 by an explicit equilateral vertex | Before synthetic axiom systems, 3D, or non-Euclidean geometry |
| `linear_algebra_core` | Reusable abstract structures connect to concrete computation | A coordinate projection on `R^2` | Kernel-zero iff injective, then a guarded finite-dimensional tranche | Before inner products, eigenvalues, determinants as a general theory, or SVD |
| `calculus` | Approximation relations become derivative and integral values only after existence and uniqueness | Epsilon-delta derivative of `x^2` | MVT application, then Riemann FTC behind separate gates | Before series, multivariable calculus, differential equations, or measure theory |

## Checked first-version endpoints

| Project | Current checked endpoint |
| --- | --- |
| Elementary algebra | Radical equation with explicit square-root domain and extraneous-root rejection |
| Sets/functions/relations | Preimage intersection, supplied two-sided inverse implies bijection, and same-parity equivalence laws |
| Number theory | Gcd/Bezout certificate and both directions of the linear-Diophantine criterion |
| Euclidean geometry | Euclid I.1 from an explicit analytic equilateral vertex |
| Linear algebra | Concrete `R^2` Gate A through kernel-zero iff injective |
| Calculus | Relational derivatives for `x^2` and affine functions, differentiability existence, and a tangent-error identity |

All six `main.lit` files pass their independent release file and module
runners. None contains a direct `trust` or local axiom. These statements do not
remove the broader trust boundary in Litex's Builtin/infer rules.

## Litex and Lean: the interface difference shown here

The mathematics in these files can also be formalized in Lean. The useful
comparison is not “which system proves more.” Lean normally places these facts
inside mature generic structures and library namespaces. These Litex first
versions instead keep the local mathematical facts, existential witnesses,
definition equations, and well-definedness premises visible in a short source
spine. For example, the number-theory file literally obtains and rescales
Bezout witnesses, while the calculus file refuses to introduce a selected
derivative before uniqueness exists.

Litex is not trying to replace Lean. It tests a different hypothesis: that a
smaller, readable, fact-oriented formal language can make checked mathematics
cheap enough for students, domain scientists, and AI agents to produce useful
formal data at scale. These scratch files are evidence for that interface
experiment, not a general superiority or soundness claim.

## Shared internal architecture

Every mature `main.lit` should eventually read in the same order:

1. **Carrier and notation layer** -- reuse Builtin carriers and operations.
2. **Concept layer** -- define objects, functions, relations, and structures in
   the form their downstream callers need.
3. **Law layer** -- prove the smallest reusable facts that make the concepts
   usable.
4. **Spine layer** -- a short sequence of named theorems with visible
   dependencies.
5. **Flagship example** -- one non-toy theorem or construction that consumes
   the earlier interfaces.
6. **Boundary note** -- disclose omitted mathematics and any remaining trust,
   axiom, or verifier boundary.

## Promotion gates

A project remains scratch until all of the following hold:

- every public concept has a real downstream use in the same project;
- the main theorem spine has no direct `trust`;
- axioms and Builtin/infer-rule dependencies are visible and justified;
- the project passes its release runner independently;
- the flagship example is mathematical consumption, not only an interface
  probe;
- the Lean comparison uses the same mathematical statement and describes an
  interface tradeoff rather than claiming general superiority; and
- repeated interfaces are promoted to `std` only after at least two real
  consumers need the same stable shape.

## Collection boundary

Calculus is included as a staged project, not as a completed core. Its checked
first version proves derivative relations for `x^2` and affine functions and
packages candidate existence as differentiability.
Selected limits/derivatives/integrals, compact-interval theorems, MVT, Riemann
integrability, and FTC enter only through the explicit gates in
`calculus/plan.md`; they must not be represented as completed by importing or
copying trusted textbook statements.

The collection still stops before probability, abstract algebra as its own
project, infinite series, multivariable analysis, measure theory, and any
cross-domain least-squares project. Those should be opened only in response to
real consumers of stable interfaces from these six projects.
