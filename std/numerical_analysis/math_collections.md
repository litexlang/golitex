# Square-root Newton iteration

For a>0 and x>0, the Newton step is (x+a/x)/2. It is positive. Its exact
residual identity is 4*x^2*(next^2-a)=(x^2-a)^2. Relative to the positive
root r=sqrt(a), 2*x*(next-r)=(x-r)^2; therefore every next iterate lies above
r. Starting above r gives decreasing iterates and a halving bound for the
nonnegative root error; a quadratic bound uses the same exact identity.

The recursive iterate starts at an arbitrary positive value. These definitions
and estimates are the first target; convergence and root selection require
explicit sequence-limit proofs. The existing sqrt(2) showcase is evidence of
reusable algebraic proof routes, not a substitute for a general proof. No
zero-reset executable branch or new derivative/limit interface is introduced.
All targets remain unverified until materialized in main.lit and recorded in
the README. Later numerical methods remain separate work.
