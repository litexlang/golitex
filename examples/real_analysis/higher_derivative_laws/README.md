# Higher derivative source laws

The example supplies independent cubic and sine derivative profiles. It then
uses the optional source addition, subtraction and scale theorems to prove
third-order candidates5,7 and20 for x^3+sin(x),x^3-sin(x),4*(x^3+sin(x)) at0.
The target functions supply no intermediate profiles. Order-zero addition is
checked independently. Prove the candidate before using the existing selector.

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/higher_derivative_laws/main.lit
```

The maintained source package is std/real_higher_order_laws. Package import and
the caller's individual statements passed the live Session; saved-file and
refusal acceptance are recorded separately in the task inventory.

The independent ordered.lit target supplies profiles for x1^2 and x2^2, then
proves order-2 path(1,1) candidates2 for their sum and6 for three times that sum
at(3,4). It also checks order-zero addition25. Run it with the same command and
ordered.lit in place of main.lit. The focused installed test checks both targets,
seven positive law uses and twelve rejected controls; each rejection is followed
by a successful Session statement. Invalid domains, coefficients, orders, paths,
missing candidates and invented numeric values remain outside the contract.
