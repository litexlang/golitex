# Litex support for common LaTeX mathematics

Date: 2026-10-18. Status: implementation roadmap; the first category-1 scalar/set increment is implemented and verified.

## Goal

Give common mathematical operations familiar from LaTeX an out-of-the-box Litex interface: an object or relation with an enforced domain, usable mathematical rules, and faithful LaTeX output. The user selected this meaning of “support”; accepting raw LaTeX source is a separate feature.

The first implementation priority is category 1. Its detailed [Obj, well-definedness, BT-rule and acceptance plan](litex-latex-phase-1.md) records the delivered increment, acceptance evidence and remaining work. This roadmap records all five categories, so completing the first phase does not imply complete mathematical coverage.

## Five work categories

| Priority/category | Mathematical scope | Work required |
| --- | --- | --- |
| **1. Common operations built from existing mathematics** | Complex conjugation; secant/cosecant; real hyperbolic functions; set symmetric difference; function composition | Native objects, domains, defining equations, bounded relationship rules, evidence and presentation. Start here. Function restriction uses existing anonymous functions. |
| **2. Selected values on existing mathematical foundations** | Suprema/infima, sequence limits, derivatives/partial derivatives in already developed models, inverse functions under appropriate hypotheses | Consolidate candidate relations, domain conditions, existence, uniqueness and selected-value interfaces. Existing relations alone do not count as an available value operator. |
| **3. Coherent operation families** | Binomial/multinomial coefficients; vector and matrix operations, inner products/norms, determinant/inverse/rank; gradients and Jacobians | Specify carriers, dimensions, result types and mutually consistent algebraic laws before wiring isolated names. |
| **4. Additional analysis foundations** | Definite/indefinite/multiple/path integrals, infinite sums/products, general function limits and limsup/liminf, general probability/expectation/variance | Develop the appropriate convergence, integrability, measure and selection contracts. Integration and convergence assumptions must remain visible. |
| **5. Context or convention must be selected first** | Extended infinity, complex argument, argmin/argmax, approximation/asymptotic notation, tensor/direct sums, closure/interior/boundary | Fix the underlying structure, branch, tolerance, limiting regime or return kind. A glyph does not uniquely specify its mathematics. |

General nth roots are adjacent to category 1, but need a separate contract for negative real inputs, parity and complex roots. Inverse hyperbolic and inverse reciprocal trigonometric functions also need explicit principal domains/branches; they are retained as follow-up scope rather than silently included in the initial real direct-function family.

## Source baseline

- [Object families](../src/ast/obj.rs) and the [object parser](../src/parse/object/primary.rs) already cover scalar arithmetic, elementary trigonometry, exponentials/logarithms, complex parts/modulus, set algebra, function spaces and finite aggregates.
- [Equality verification](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/README.md) separates mathematical rules from object-definition unfolding, stored facts and identity.
- [Single-variable calculus](../showcases/math_concepts_in_litex/7_calculus/main.lit), [partial derivatives](../showcases/math_concepts_in_litex/11_multivariable_calculus_in_nutshell/main.lit) and [sequence limits](../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit) provide source-owned interfaces. These are not automatically available in a fresh context.
- Native least-upper-bound/greatest-lower-bound certificates and theorem calls already exist; public selected `sup`/`inf` objects are a different interface.
- [LaTeX conversion](../src/compile_to_latex/README.md) is parse-only. Successful output cannot establish mathematical truth or well-definedness.

The original inventory was based on source inspection. The later implementation and verification are recorded in the companion phase-1 receipt; unimplemented roadmap entries remain proposals.

## Completion standard

For each operation, require all of the following:

1. A precise mathematical contract: input carriers, guards, output kind and relevant conventions.
2. A directly usable public name and representation, without requiring copied showcase definitions.
3. Well-definedness and callable/return membership support, including nested use.
4. Defining equations and the listed relationships, with bounded proof search and retained premise evidence.
5. Positive, false-result and missing-domain/invalid-domain controls.
6. Substitution, alpha normalization, identity/IR, diagnostic output, JSON and LaTeX support.
7. An explicit compiler/replay boundary: supported proofs replay correctly; unsupported ones fail closed.
8. Maintained examples, live documentation and current-source acceptance evidence.

## Current delivery

2026-10-18: the user authorized the concrete phase-1 Obj proposal and then deferred `compose`/`restrict`. The first increment implements the ten scalar/set objects with core equations and checked domains. See the [phase-1 progress and remaining rules](litex-latex-phase-1.md) and [current language documentation](../docs/native-elementary-operators.md). This does not complete every relationship in category 1.

Later the same day, the user removed native restriction from scope and requested a careful composition design including `f ∘ g`. The [composition design](litex-function-composition.md) proposes `compose(f,g) = f ∘ g`, with unary outer function, fixed positive-arity inner function, preserved inner guards and complete domain, and right-associative notation. It records Obj, proof evidence, BT laws, name migrations and acceptance steps; implementation remains pending. Restrictions continue to use `fn(x S) B {f(x)}` or an explicitly guarded multi-argument anonymous function.

## Delivery order

1. Complete category 1 in the small vertical increments specified in [phase 1](litex-latex-phase-1.md). Each increment includes Obj, WD, laws, evidence, output and regression controls.
2. Consolidate existing bound/limit/derivative interfaces into category-2 public operations, preserving their actual mathematical domains and proof status.
3. Plan category-3 families separately, starting with their carriers and operations rather than isolated notation.
4. Establish the category-4 mathematical prerequisites and decide category-5 conventions before implementing their public interfaces. Dependencies can reorder later increments; they do not remove scope from this roadmap.

## Decision and authority boundary

The user requested this roadmap and a detailed category-1 implementation plan, including Obj and BT relationships. The companion file therefore gives concrete AST proposals. It does not treat that planning request as blanket approval to change protected AST or Env/Runtime structures. Actual implementation must use the approved concrete shape and preserve unrelated worktree changes.

Keep `scripts/` local-only. No repository creation, commits, publishing, local textbook verification or release gating is part of this planning task.
