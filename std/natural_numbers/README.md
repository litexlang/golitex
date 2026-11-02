# Natural recursion and discrete existence

This module constructs sequences by index-dependent recursion on any set and
proves their unique existence. It also supplies unique natural predecessors
and Euclidean division with a natural quotient and bounded natural remainder.
It reuses native `N`, arithmetic, induction, `quot` and `%`.

## Import and use

```ini
[import std]
Natural = natural_numbers
[alias]
nat = Natural::main
[export]
main = "./main.lit"
```

The step has two inputs: the current index and the previous value. This example
constructs the squares by adding successive odd numbers:

```litex
have fn square_step(k N,x N) N = x + 2*k + 1
have fn squares(k N) N = k^2

claim:
    ? forall k N:
        squares(k+1) = square_step(k,squares(k))
    squares(k+1) = (k+1)^2 = k^2+2*k+1 = square_step(k,squares(k))

by def $nat::is_natural_recursion(N,0,square_step,squares)

claim:
    ? forall n N:
        \nat::natural_recursion<N,0,square_step>(n) = n^2
    release thm nat::natural_recursion_unique(N,0,square_step,squares,n)
    \nat::natural_recursion<N,0,square_step>(n) = squares(n) = n^2
```

## Interfaces

`\nat::natural_recursion<S,start,step>` is an actual complete function from
`N` to `S`, starting at `start` and obeying `a(n+1)=step(n,a(n))`.
The supplied start belongs to `S`, and the step is complete on `N` and `S`.
No nonemptiness premise is needed beyond the supplied start. The carrier may
contain sets or other nonnumeric objects.

| Theorem after `nat::` | Contract |
| --- | --- |
| `natural_recursion_equations(S,start,step,n)` | Initial equation and successor equation at `n in N`. |
| `natural_recursion_satisfies(S,start,step)` | The constructed function satisfies `is_natural_recursion`. |
| `natural_recursion_unique(S,start,step,a,n)` | A complete function satisfying the same equations agrees with the construction at every supplied natural index. |
| `natural_recursion_exists_unique(S,start,step)` | Exactly one complete `N -> S` function satisfies those equations; uniqueness is equality of functions. |
| `natural_predecessor_unique(a)` | Every `a in N+` has exactly one `b in N` with `b+1=a`. |
| `natural_division_exists(n,q)` | For `n in N`, `q in N+`, supplies `m,r in N` with `r<q` and `n=m*q+r`. |
| `natural_division_unique(n,q,m,r,u,v)` | Two such decompositions with both remainders below `q` have equal quotients and remainders. |

For explicit evaluation or congruence of a materialized template, expose its
complete function interface when needed:

```litex
release thm fn_set_member(\nat::natural_recursion<N,0,square_step>,fn(k N) N)
```

## Evidence and boundaries

On 2026-10-31 the existing release executable, reporting `1.1.10-beta`, accepted
the nine source declarations in strict mode. An independent strict import
accepted all seven theorem contracts at their full domains, the square closed
form, an index-dependent set-valued recursion, and unit/zero/exact/remainder
division cases. Six final controls rejected zero predecessor, zero divisor,
unbounded remainder, negative index and incorrect initial conditions. Process
records are local development material in `experiments/`, outside this module.

These results cover the source needs of Tao, *Analysis I*, 2.1.16, 2.2.10 and
2.3.9; quotient/remainder uniqueness is an additional reusable law. Existing
native arithmetic and induction cover the remaining chapter foundations and
laws, separately checked in the local source audit. No alternative natural
number model, general well-founded recursion, standalone exercise collection,
kernel change, source trust, user axiom or Lean replay is included.
