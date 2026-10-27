# Real higher derivative laws

## Linear combinations of candidates

A finite derivative candidate carries an actual nested-domain certificate.
Linearity combines two such certificates stage by stage: intersect their
regions, combine their real values, and preserve the native derivative
neighborhood in the intersection using the minimum of two positive radii.
The input functions f,g,h share one complete actual domain D; the internal
certificate regions may differ.

The public form is a source theorem, not an Obj, existence selector or automatic
WD rule. `nth_derivative_linear_combination(D,k,f,g,h,p,a,b,A,B)` consumes the
candidate A for f and B for g, plus h(x)=a*f(x)+b*g(x), and returns candidate
a*A+b*B. The ordered counterpart also takes dimension n and a length-k path
for a single vector input. A missing candidate remains a missing premise even
when its coefficient is zero. Addition, subtraction and scaling are source
specializations with fixed names and contracts.

## Common actual neighborhoods

The first-order source lemmas permit different source domains and an explicit
common target domain with a real or coordinate neighborhood. The ordered lemma
restricts both functions to that exact target before reusing native product
and addition laws. Scalar coefficients remain real; vector-valued output is
not part of these contracts. An isolated target point supplies no such radius.

## Dependencies and verified scope

The module imports the existing `real_multivariable` certificate, uniqueness,
selector and locality interfaces. Native derivative/partial definition rules,
first-order scale/product/addition laws and constant strategies are reused.
There is no new mathematical kernel schema or state owner. Authoring Session
proofs cover arbitrary finite k; package-import and caller acceptance are
recorded separately in the task's maintained local inventory.
