# Mathematical design of the inequality experiments

The six source problems keep their original real domains, hypotheses, inequality
signs, and additional tasks. Five now have checked standalone proof files. No
executable module manifest or external mathematical library is used.

## IMO 1995 P2

The reciprocal substitution reduces the target to the homogeneous rational
inequality sum x^2/(y+z)>=3/2 with positive x,y,z and xyz=1. The dependency chain is
a minimum-variable cubic certificate, three-variable AM-GM, denominator
nonzero evidence, the squared-difference certificate, and reciprocal transport.
The final target keeps all three original summands. A numerator or denominator
sign assumption introduced solely to make the target pass would be invalid;
all required signs are derived from the original positivity hypotheses.

## IMO 1983 P6

The cyclic quartic is reduced to two sorted-side cases. With smallest side m
and nonnegative gaps x,y, ascending order has the bound m^2*(x^2+y^2).
Reverse order has bound m^2*x^2 and uses x<m, derived from the strict triangle
inequality. Their positive factors force gaps to zero at equality. The final
source states the original inequality, proves that equality forces a=b=c,
and proves that equal sides attain zero. Dropping the triangle hypothesis,
using only one side order, or omitting equality cases would change coverage.

The local theorem names are proof decomposition interfaces, not a proposed
standard library. They serve the two standalone experiment files only.

## IMO 2001 P2

Use weighted quadratic and reciprocal Cauchy certificates, followed by the
weighted squared-gap identity for the cubic bound. Square-root signs and squares
are derived from positive radicands. The final statement keeps the three original
radical fractions. Their main proof body is required in the current tested context.

## IMO 2005 P3

The rational single-term comparison uses a square certificate rather than cases
on whether x is above or below one. The product bound then supplies 1/x<=yz.
A sum-of-squares comparison closes the cyclic sum. All three original summands
and the weak product condition xyz>=1 remain intact.

## IMO 2006 P3

The difference substitution connects a discriminant certificate to a quartic
balance certificate. Taking squared bounds back to absolute values requires a
nonnegative right side. The extremizing triple proves a separate lower-bound
claim for every universally admissible M. Both parts are required for the least
constant result; a true but larger upper constant alone would be incomplete.
