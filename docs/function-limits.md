# Finite-point real function limits (preview)

`$has_limit_at(f,x0,L)` states that the unary real-valued function `f`
converges to the real value `L` as inputs in its actual domain approach the
real point `x0`, excluding `x0` itself. The domain includes every callable
guard. It must have points arbitrarily close to `x0` other than `x0`.
An empty or isolated domain cannot produce a limit by vacuous control.

`lim(f,x0)` selects a real value only after a concrete candidate or existence
of a finite candidate has been proved. WD consumes that evidence; it does
not inspect a body or invoke convergence theorems to guess the answer.
Even a constant function requires an explicit convergence proof:

```litex
have fn c(x R) R = 3
release thm fn_limit_at_real_accumulation(0)
release thm fn_limit_at_constant(c,0,3)
lim(c,0) = 3
lim(c,0) + 2 = 5
```

Without the constant-limit theorem, both `lim(c,0)=3` and
`0*lim(c,0)=0` lack WD evidence. A proof at one point does not provide a
limit at another point. Existing one-argument [sequence limits](sequence-limits.md)
retain their own interface.

After a candidate value is proved, selected-value equality can use its stored
value equality or exact closed arithmetic: a proved candidate `3^2` permits
`lim(square,3)=9`. This calculation consumes the candidate; it does not
establish convergence from a function body.

## Definition and explicit proofs

Write `D` here for the actual complete unary input domain, including guards.
It is mathematical shorthand, not a new public domain operator. Require real
inputs and outputs. An ambiguous complete-domain view needs an explicit
unambiguous function value before this operation can be used.

The candidate has two defining clauses. Mathematical layouts below use
existing existential and preimage/set-inclusion forms:

```text
forall r R+:
    exist x D st {0 < abs(x-x0) and abs(x-x0) < r}

forall epsilon R+:
    exist delta R+ st {{x D: 0 < abs(x-x0) and abs(x-x0) < delta} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
```

Prove both clauses and use `by def $has_limit_at(f,x0,L)`, or explicitly
invoke `fn_limit_at_from_epsilon(f,x0,L)`. No selected value appears in
these premises. Each existential body remains quantifier-free.

The point need not belong to the domain. For
`have fn f(x R: x != 0) R = x^2/x`, the punctured proof at zero chooses
`x=r/2` for accumulation and `delta=epsilon` for control. It uses
`x^2/x=x` only for legal nonzero inputs; it never calls `f(0)`.
See the [complete explicit proof](../examples/wd/real_function_limit_at.lit).

These are relative-domain limits. At an endpoint of `R+`, an ordinary
candidate can exist without inputs on the left. This feature does not supply
left/right limit operators or equate an absent side with an existing one.

## Explicit builtin theorems

Arguments below are in call order. `x0,A,B,L,c` are real; `r,epsilon` are
positive real; `m` is natural. Each theorem checks and retains its premises.
`D_f` denotes the complete domain of `f`; `U(D,x0,r)` denotes its punctured
radius-r neighborhood. Neither is an extra public constructor.

| Call | Premises and result |
| --- | --- |
| `fn_limit_at_real_accumulation(x0)` | Proves the displayed accumulation clause for all of `R` |
| `fn_limit_at_from_epsilon(f,x0,L)` | Accumulation and epsilon-delta control; produces candidate L |
| `fn_limit_at_accumulation(f,x0,L)` | Candidate L; exposes the accumulation clause for the actual domain |
| `fn_limit_at_control(f,x0,L,epsilon)` | Candidate L and positive epsilon; produces a positive delta and the control inclusion |
| `fn_limit_at_constant(f,x0,c)` | Accumulation and `f(x)=c` for every legal x; produces candidate c |
| `fn_limit_at_identity(f,x0)` | Accumulation and `f(x)=x` for every legal x; produces candidate x0 |
| `fn_limit_at_unique(f,x0,A,B)` | Both candidates at the same point; produces A=B |
| `fn_limit_at_exists(f,x0,L)` | Candidate L; produces existence of a finite real candidate |
| `fn_limit_at_selected(f,x0)` | Proved finite existence; produces `$has_limit_at(f,x0,lim(f,x0))` |
| `fn_limit_at_neg(f,h,x0,A)` | Candidate A, common domain and `h(x)=-f(x)`; produces candidate -A for h |
| `fn_limit_at_abs(f,h,x0,A)` | Same pattern with absolute values |
| `fn_limit_at_scale(f,h,x0,A,c)` | Common domain and `h(x)=c*f(x)`; produces c*A |
| `fn_limit_at_power(f,h,x0,A,m)` | Common domain and `h(x)=f(x)^m`; produces A^m |
| `fn_limit_at_add(f,g,h,x0,A,B)` | Both candidates, common domains and `h(x)=f(x)+g(x)`; produces A+B |
| `fn_limit_at_subtract(f,g,h,x0,A,B)` | Corresponding difference law |
| `fn_limit_at_multiply(f,g,h,x0,A,B)` | Corresponding product law |
| `fn_limit_at_divide(f,g,h,x0,A,B)` | B!=0, g(x)!=0 for every legal x, common domains and `h(x)=f(x)/g(x)`; produces A/B |
| `fn_limit_at_local_equal(f,g,x0,L,r)` | Candidate L for f, accumulation for g, `U(D_g,x0,r)` contained in D_f, and equality there; produces candidate L for g |
| `fn_limit_at_compare(f,g,x0,A,B,r)` | Both candidates, common domain and f(x)<=g(x) on U; produces A<=B |
| `fn_limit_at_squeeze(f,g,h,x0,L,r)` | Candidates L for f,h, common domains and f(x)<=g(x)<=h(x) on U; produces candidate L for g |
| `fn_limit_at_eventually_positive(f,x0,L)` | Candidate L>0; produces a neighborhood included in `preimage_set(f,R+)` |
| `fn_limit_at_eventually_nonzero(f,x0,L)` | Candidate L!=0; produces a neighborhood included in `preimage_set(f,R*)` |

Algebra takes an explicit output function `h`. Its pointwise equation is a
checked premise, not a body pattern or an automatic function constructor.
Common-domain premises compare the actual domain sets. Use explicit
restrictions/local transport when domains differ; a BT does not silently
intersect or widen them.

A nonzero denominator limit does not make all calls to the denominator
nonzero. A legal guarded quotient may be handled on an explicit common
restricted domain. Conversely `x^2/x` at zero uses local equality; the
quotient theorem with denominator limit zero does not apply.

Local equality requires source call legality throughout a target punctured
neighborhood and target accumulation. Agreement only on a sparse intersection
of domains is insufficient. Comparison conclusions are non-strict, even if a
punctured premise is strict. Two punctured limits alone do not justify
composition when the inner function keeps hitting the excluded outer point.

## Boundaries and evidence

The negative relation `not $has_limit_at(f,x0,L)` is logical negation, not a
search failure. Its WD checks carriers/callability, not convergence or
accumulation in advance, so negations on empty/isolated domains are meaningful.

`has_limit_at` and the explicit theorem names are reserved. `lim` accepts
one sequence argument or two function/point arguments. It is an object
constructor, not a first-class callable value.

LaTeX shows the approach point and actual function domain, with a fresh
display binder. As elsewhere, `-latex` is parse-only and reports
`verified=false`; output does not establish convergence. Native function-limit
proof replay to Lean remains unsupported and fails explicitly.

Function limits at infinite inputs, infinite output values, one-sided limits,
limsup/liminf and general transcendental continuity remain later increments.
