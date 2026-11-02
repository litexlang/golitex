# Power and root proof dependencies

The module has 45 declarations: 44 named theorems and one actual set template.
Native real numbers, scalar powers and logarithms are reused. Explicit e>1,
e>0 and e!=1 facts enable the existing natural-log power/product identities.
Log injectivity follows from the existing inverse with base e. These checked
identities prove native power addition, iteration, negative exponents, product
powers and nonzero-exponent injectivity on positive bases for arbitrary real
exponents. No new value-level power or unproved algebra premise is introduced.

The natural-power absolute-value theorem supplies nonnegativity for nonnegative
bases, including exponent zero. Weak natural-power order follows by induction
from zero; strict positive-natural order factors off one positive power. Order
reflection follows by contradiction. This route does not depend on unsupported
automatic real/rational power-order search.

The actual native x^(1/n) is real and nonnegative for x>=0, n in N+. Separate
zero/positive cases and the proved positive-base iteration law give its power
equation. The same cases prove uniqueness of nonnegative roots. Positive roots
and their converse sign property implement the corrected zero boundary.
Products and nested roots publish each real-carrier fact before forming and
composing the next expression. Ordinary source proofs supply those facts; no
scenario-specific WD branch or kernel repair is used.

The template's input domain contains nonnegativity, and its output is in
power_set(R). Membership characterizes the actual set y>=0 and y^n<=x. Strict
natural-power order rules out any member greater than the native root, so
the root is a maximum. The real-set upper-bound interface from extended_reals
then gives nonemptiness, boundedness and the native least-upper-bound certificate.
An explicit existential certificate precedes the partial native sup selector,
and native uniqueness identifies that selector with the root. This establishes
the source supremum definition, not merely abstract root existence.

Root order, products and composition use the proved power equation, natural
power order and root uniqueness. Integer exponent differences yield index
monotonicity at bases>1 and 0<base<1; root(0) and root(1) remain constant.
General positive-base power iteration proves the integer-fraction formula and
representation independence for all integer numerators. Actual reduced
fractions turn positive rational exponents into positive integer numerators
and denominators. Natural-power order and reciprocal exponentiation give
strict rational base order in both directions; rational exponent differences
give both exponent-order directions for bases above/below one.

Exact source 5.6.1-5.6.3 audits include every 4.3.10/4.3.12 clause at real
domains, including zero, negative bases and negative integer exponents. They
distinguish native algebra from the std order/absolute-value proofs. Independent
consumers cover all public contracts, complete README examples, source-sign
corrections and nearest false/domain boundaries. The author's corrected
5.6.6(c),(e) and additional 5.6.9(f) are recorded in the experiment scope ledger.
