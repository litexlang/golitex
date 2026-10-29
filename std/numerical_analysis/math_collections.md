# Square-root Newton iteration

For a>0 and x>0, the Newton step is (x+a/x)/2. A positivity proof establishes
its return carrier before defining the operation. The recursive iterate starts
at an arbitrary positive value, with natural index zero equal to that seed.
The positive-index native sequence uses the same iterate values at k>=1.

The scaled update gives the exact residual identity
4*x^2*(next^2-a)=(x^2-a)^2. Relative to r=sqrt(a), the exact identity
2*x*(next-r)=(x-r)^2 proves next>=r. Above r, the update decreases and its
error is nonnegative and at most half the preceding error. The same identity,
using x>=r>0, gives the quadratic bound error_next<=error^2/(2*r).

Every first update is above r. Induction then gives
u(n)-r<=(u(1)-r)/2^(n-1) for n>=1. The convergence proof uses the existing
real_series nonnegative-geometric limit, scales it by twice the first error,
squeezes the error sequence between zero and that bound, and adds the constant
root sequence. Function extensionality identifies this sum with the actual
native sequence. This reuses the sequence-limit interfaces; it introduces no
new derivative or limit definition. The root is also checked as a fixed point.

Dependency spine: positive real arithmetic and sqrt -> positive update ->
recursive iterate -> exact identities -> one-step estimates -> iterate bounds;
real_series geometric decay and native sequence-limit laws -> error squeeze
-> convergence to the root. These are definition, carrier, well-definedness,
proof and import edges. No arbitrary witness, root selector or executable
zero-reset branch is added.

All results above are materialized in main.lit. The README records 12 source
theorems, the strict 17-statement source gate, a 34-statement imported consumer
and seven fresh-Session refusals. Exact real arithmetic is the scope;
rounding/stability, arbitrary-function Newton and other numerical methods
remain separate work.
