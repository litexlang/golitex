# Rational and real sequence limits

This optional bridge constructs the actual real-valued function
`\bridge::rational_tail_as_real<start,a>(n)=a(n)` on {j Z:j>=start}.
The original rational function retains its complete integer-tail domain.
The generic real_sequences module has no dependency on this bridge.

```ini
[import std]
Bridge = rational_sequence_limits
Rational = rational_sequences
Real = real_sequences
[alias]
bridge = Bridge::main
rseq = Rational::main
rs = Real::main
[export]
main = "./main.lit"
```

`rational_cauchy_is_real_cauchy` and `real_cauchy_is_rational_cauchy`
prove Tao Analysis I 6.1.4 in both directions. The forward proof uses rational
density to choose a positive rational radius below each positive real radius.
It does not use real completeness or a future Cauchy-convergence converse.

`rational_native_limit_is_genuine` transports any actual native limit value
to the source epsilon relation. Cauchy representatives have a unique genuine
real limit; `rational_cauchy_selected_limits_agree` identifies their native
selected value with `\rs::real_tail_limit<start>` on the actual real-valued
sequence, as in 6.1.15. Boundedness agrees in both directions; a nonnegative
rational bound may be zero, while real existential boundedness has a positive
witness. An Archimedean positive integer enlarges an arbitrary real bound.

The following complete caller verifies a negative-start rational representative,
both Cauchy definitions and both selected limit values:

```litex
release thm rseq::rational_constant_sequence_is_cauchy(-5,3)
release thm bridge::rational_cauchy_is_real_cauchy(-5,\rseq::rational_constant_sequence<-5,3>)
release thm bridge::real_cauchy_is_rational_cauchy(-5,\rseq::rational_constant_sequence<-5,3>)
release thm rseq::rational_constant_sequence_real_limit(-5,3)
release thm bridge::rational_native_limit_is_genuine(-5,\rseq::rational_constant_sequence<-5,3>,3)
release thm bridge::rational_cauchy_native_limit_exists(-5,\rseq::rational_constant_sequence<-5,3>)
release thm bridge::rational_cauchy_real_tail_converges(-5,\rseq::rational_constant_sequence<-5,3>)
release thm bridge::rational_cauchy_selected_limits_agree(-5,\rseq::rational_constant_sequence<-5,3>)
release thm rs::real_tail_limit_value(-5,\bridge::rational_tail_as_real<-5,\rseq::rational_constant_sequence<-5,3>>,3)
\rs::real_tail_limit<-5>(\bridge::rational_tail_as_real<-5,\rseq::rational_constant_sequence<-5,3>>)=3
```

No quotient-real construction, parallel rational arithmetic, trusted equality,
new axiom, kernel rule or function-domain identification is added. Exact
source correspondence and strict independent consumers remain in experiments/.
