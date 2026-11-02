# Real absolute-error estimates

This module defines epsilon-closeness on real scalars and proves the estimates
used in Tao, *Analysis I*, 4.3.4 and 4.3.7. Positive radii belong to the predicate
contract. Rational arguments specialize the same predicate; the rational
identity theorem quantifies only positive rational radii, as in the source.
Zero-inclusive natural powers and nonzero-base integer powers also preserve
absolute values.

```ini
[import std]
Approximation = real_approximation
[alias]
approx = Approximation::main
[export]
main = "./main.lit"
```

`is_epsilon_close(x,y,epsilon)` means `abs(x-y) <= epsilon`, with `x,y in R`
and `epsilon in R+`. It uses a closed error bound. Zero and negative radii
are outside this interface.

All theorem names below follow `approx::`.

| Theorem | Contract |
| --- | --- |
| `absolute_value_two_sided_bounds(t,b)` | `abs(t)<=b` implies `-b<=t<=b`. Both arguments are real. |
| `epsilon_close_reflexive(x,epsilon)` | A point is close to itself for every positive radius. |
| `epsilon_close_identity(x,y)` | Closeness for every positive real radius implies equality. |
| `rational_epsilon_close_identity(x,y)` | For rational points, closeness for every positive rational radius implies equality. |
| `epsilon_close_symmetric(x,y,epsilon)` | Reverse the two points. |
| `epsilon_close_transitive(x,y,z,epsilon,delta)` | Compose two bounds, adding their radii. |
| `epsilon_close_addition(x,y,z,w,epsilon,delta)` | Add two approximate pairs, adding the error bounds. |
| `epsilon_close_subtraction(x,y,z,w,epsilon,delta)` | Subtract two approximate pairs, adding the error bounds. |
| `epsilon_close_monotone(x,y,epsilon,enlarged)` | Enlarge a positive radius when `epsilon<=enlarged`. |
| `epsilon_close_between(center,left,right,point,epsilon)` | If `left<=point<=right` and both endpoints are close to the center, so is the point. Swap endpoints for the reverse order. |
| `epsilon_close_scaling(x,y,z,epsilon)` | Scale by nonzero real `z`; the radius becomes `epsilon*abs(z)`. |
| `epsilon_close_multiplication(x,y,z,w,epsilon,delta)` | The product error radius is `epsilon*abs(z)+delta*abs(x)+epsilon*delta`. |
| `absolute_value_natural_power(x,n)` | `abs(x^n)=abs(x)^n` for all real `x` and natural `n`, including `0^0=1`. |
| `absolute_value_integer_power(x,n)` | The same identity for nonzero real `x` and every integer exponent. |
| `bounded_product_difference(x,y,z,w,x_bound,w_bound,epsilon)` | From both pair errors<=epsilon and abs(x)<=x_bound, abs(w)<=w_bound, obtain abs(x*z-y*w)<=epsilon*(x_bound+w_bound). Raw real bounds allow zero. |
| `reciprocal_difference_bound(x,y,c,d)` | For nonzero real x,y and positive c,d bounded by their magnitudes, abs(1/x-1/y)<=abs(x-y)/(c*d). |

## Example: the mixed term is necessary

With the configuration above, this complete caller obtains a sharp product
bound. Omitting the mixed term would give radius two, which is false here.

```litex
by def $approx::is_epsilon_close(1,2,1)
release thm approx::epsilon_close_multiplication(1,2,1,2,1,1)
1*abs(1)+1*abs(1)+1*1 = 3
$approx::is_epsilon_close(1,4,3)
```

These are scalar estimates. They introduce no replacement arithmetic, norm,
limit selector, rounding convention or unchecked assumption. Drafts, exact
verification receipts and false/ill-typed controls remain in the source-ordered
`experiments/` workspace.


The additional scalar estimates support Cauchy products and reciprocals. The
product helper bounds x and w, matching `xz-yw=x(z-w)+w(x-y)`. The following
complete caller checks a sharp product, zero error and opposite-sign inverses:

```litex
release thm approx::bounded_product_difference(1,2,1,2,1,2,1)
release thm approx::bounded_product_difference(0,0,0,0,0,0,0)
release thm approx::reciprocal_difference_bound(-2,4,2,4)
```
