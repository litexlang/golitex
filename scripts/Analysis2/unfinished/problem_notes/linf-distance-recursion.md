# l-infinity distance recursion

Attempt: define a recursive `linf_distance_partial` inside a template over
`n,x,y`, then instantiate it at `n`. The template declaration reports success,
but the wrapper use fails exactly with
`WellDefinedError: function 'linf_distance_partial' not defined`.

Current workaround: `linf_distance` is selected from the unique finite
coordinate maximum relation with a visible `trust`. Desired behavior: retain
the recursive local function binding during template instantiation. Primary
blocker: `kernel_problem`.
