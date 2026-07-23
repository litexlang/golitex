# Selected metric limit

Attempt 1 used a generic `have fn ... by exist!` returning an element of the
parameter carrier `X`; it failed with
`forall parameter types must all be Obj`. Attempt 2 put `X,dist` in a template;
the declaration succeeded, but its immediate selected-limit fact was unknown
to the caller.

Current workaround: Chapter 1 exposes `has_metric_limit`,
`is_metric_convergent`, and `metric_limit_unique`, but no selected value
function. Desired behavior: propagate the unique-selection certificate from
the instantiated template. Primary blocker: `kernel_problem`.
