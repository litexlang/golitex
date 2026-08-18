# Concept Inventory

| Concept | Litex form | Why it is here |
| --- | --- | --- |
| candidate derivative at a point | epsilon-delta `prop` | checked analytic meaning and proof-facing graph relation |
| differentiability at a point | existential `prop` | domain condition for selecting a derivative value |
| derivative value | `have fn ... by exist!` | exposes the unique candidate as `derivative_at(f, x)` |
| ODE right-hand side | `have fn` | defines `y'=F(x,y)` |
| solution at a point | existential and selected-value `prop` interfaces | connects either a candidate slope or `derivative_at(f,x)` to the RHS |
| quadratic candidate family | `have fn` | makes the integration constant visible |
| initial-value selection | `thm` | proves `y(0)=y₀` forces `c=y₀` |
| fixed IVP solution | `thm` + initial value | checked flagship example |

The showcase proves uniqueness of derivative values but stops before ODE
solution existence/uniqueness theorems, systems, stability, phase portraits,
and boundary-value problems. The selected derivative function is intentionally
guarded by `is_differentiable_at`; it is not an unconditional total derivative
operator on every function and point.
