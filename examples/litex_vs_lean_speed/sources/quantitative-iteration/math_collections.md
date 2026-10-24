# Mathematical design

All objects are exact real values. The two languages must retain the same domains and quantification. Lean may totalize an underlying function outside the stated domain, but the compared theorem is restricted to the same legal arguments.

## Parametric Newton step

For a>0 and x>0 set N_a(x)=(x+a/x)/2. Positivity follows from positivity of both summands. Expanding a square after multiplying by 4*x^2 gives 4*x^2*(N_a(x)^2-a)=(x^2-a)^2. The right side is nonnegative and the factor is positive, so the updated square is at least a. This is a one-step theorem; it does not assert existence or convergence of an infinite orbit. Zero is excluded from the input domain.

## Scalar quadratic gradient descent

For a>0, center b, and step eta with 0<eta*a<2, set F(x)=a*(x-b)^2/2 and G(x)=x-eta*a*(x-b). Algebra gives G(x)-b=(1-eta*a)*(x-b) and F(x)-F(G(x))=eta*a^2*(2-eta*a)*(x-b)^2/2. All factors are nonnegative, and the drop is positive if x differs from b. Equality at b and failure outside the step-size regime are boundaries. This is a genuine scalar quadratic, not a theorem for arbitrary smooth objectives.

## Perturbed geometric recurrence

Given a real-valued sequence err on natural indices, 0<q<1 and an arbitrary real forcing term delta, assume err(k+1)<=q*err(k)+delta. Induction and the finite geometric identity imply err(n)<=q^n*err(0)+delta*(1-q^n)/(1-q). The initial experiment assumed delta>=0; an executed strengthening removed this unused premise on both sides. Nonnegative delta is the usual error-budget interpretation, rather than a requirement of the algebraic theorem. Nonnegativity of err is also unnecessary. The bound is conditional on a supplied sequence and recurrence; it does not construct an orbit or formalize a root-finding algorithm. The q=1 boundary has a different, linear-in-n bound and is excluded from this formula.

All three interfaces now have executed strict Litex and native Lean proofs; the archived hashes and receipts are in ../../results/quantitative-iteration-*.json. They reuse arithmetic/functions/induction and add no native mathematical feature or trusted rule. The implemented Litex sequence binder is named err: e and i are reserved builtin names in the measured executable.
