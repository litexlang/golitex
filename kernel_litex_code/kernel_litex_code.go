// Copyright Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package kernel_lib_litex_code

var PipelineInitCode = `
know forall x2, y2 R: x2 != 0, y2 != 0 => x2 * y2 != 0
know forall x, y R: x * y = 0 => x = 0 or y = 0

know:
	forall q Q: exist x Z, y N_pos st x / y = q
	forall q Q_pos: exist x N_pos, y N_pos st x / y = q
	forall q Q_neg: exist x Z_neg, y N_pos st x / y = q

let fn sqrt(z R) R:
	z >= 0
	=>:
		sqrt(z) ^ 2 = z
		sqrt(z) >= 0

know forall z R: z > 0 => sqrt(z) > 0
know sqrt(0) = 0

know forall x, y R, z N => (x * y)^z = x^z * y^z

know forall x, y, z R: z != 0, x / z = y => x = y * z, x = z * y

know forall x, y, z R, n N: x = (y * z) => x^n = y^n * z^n

know:
	forall x, y Z, z N:
		z != 0
		=>:
			(x + y) % z = (x % z + y % z) % z

know forall x, y Z, z N: z !=0, x % z = 0 => (x * y) % z = 0

know forall x, z N: z != 0, x < z => x % z = x

know forall x, y N: y != 0, x < y => x % y = x

know forall x, y, z R: z != 0, x * z = y => x = y / z

know forall x, y, z R: x + y = z => x = z - y

know forall x,y R: x + y = 0 => x = -y

# TODO: 已经放到 Std/Int/main.lit 中
know forall x,y Z => $in(x+y, Z), $in(x-y, Z), $in(x*y, Z)
	
know forall x, y, z R: x + y = z => y + x = z

know forall x, y, z R: x * y = z => y * x = z

let fn abs(x R) R
know:
	forall x R:
		x > 0
		=>:
			abs(x) = x
	forall x R:
		x < 0
		=>:
			abs(x) = -x
	abs(0) = 0
	forall x R:
		x != 0
		=>:
			abs(x) > 0
	forall x R: x >= 0 => abs(x) = x

know forall x R: x > 0 or x < 0 => x != 0

# 必须要有，否则不能说明有限集合的子集还是有限集合
know imply finite_set_subset_is_finite_set(s1 finite_set, s2 set):
	forall x s2:
		x $in s1
	=>:
		$is_finite_set(s2)

know forall x N: x != 0 => x > 0

know forall x, y R: x > 0, y > 0 => x ^ y $in R, x ^ y > 0, x * y > 0

know forall x Z => x $in Q, x $in R

know forall x N_pos => x $in N, x >= 1, x > 0, x $in Q, x $in R
know forall x Z: x > 0 => x $in N_pos
know forall x Z: x <= 0 => not x $in N_pos

"""
have fn_set seq(s set):
	fn (n N_pos) s

have fn_set finite_seq(s set, n N_pos):
    fn (x N_pos) s:
    	dom:
        	x <= n

let fn finite_seq_sum(n N_pos, a finite_seq(R, n), k N) R:
    dom:
        k <= n

know:
    forall n N_pos, a finite_seq(R, n), k N: k < n => finite_seq_sum(n, a, k+1) = finite_seq_sum(n, a, k) + a(k+1)
    forall n N_pos, a finite_seq(R, n) => finite_seq_sum(n, a, 1) = a(1)

let fn finite_seq_product(n N_pos, a finite_seq(R, n), k N) R:
    dom:
        k < n

know:
    forall n N_pos, a finite_seq(R, n), k N: k < n => finite_seq_product(n, a, k+1) = finite_seq_product(n, a, k) * a(k+1)
    forall n N_pos, a finite_seq(R, n) => finite_seq_product(n, a, 1) = a(1)
"""


know forall m N_pos => m - 1 $in N

know forall a, b R => abs(a * b) = abs(a) * abs(b)

know forall a R, b R: not a <= b => a > b

know forall a R, b R: a > b => not a <= b

know forall a R => abs(a) = abs(-a)

know:
	forall a R, b R:
		- a = b
		<=>:
			a = -b

know forall a R: a > 0 => abs(-a) = a
        
know forall a, b, c R: b > 0, a > b => c * a > c * b

know forall a R => 1^a = 1

know forall a, b, c R: a < b - c => a + c < b
know forall a, b R: b > 0 => a - b < a

know imply subtraction_preserves_inequality_with_positive_term(a R, b R, c R):
    a < b - c
    c > 0
    =>:
        a < b

know:
	forall x, y R: y > 0 => x + y > x
	forall x, y R: y > 0 => x - y < x
	forall x, y R: y < 0 => x + y < x
	forall x, y R: y < 0 => x - y > x

	forall x, y R: x > 0 => x + y > y
	forall x, y R: x < 0 => x + y < y
	forall x, y R: x >= 0 => x + y >= y
	forall x, y R: x <= 0 => x + y <= y

	forall x, y R: y >= 0 => x + y >= x
	forall x, y R: y >= 0 => x - y <= x
	forall x, y R: y <= 0 => x + y <= x
	forall x, y R: y <= 0 => x - y >= x

know:
	forall x, y R => x >= y <=> y <= x
	forall x, y R => x > y <=> y < x

	forall x, y R: not x > y => x <= y
	forall x, y R: not x < y => x >= y
	forall x, y R: not x >= y => x < y
	forall x, y R: not x <= y => x > y
	forall x, y R: not x = y, not x > y => x < y
	forall x, y R: not x = y, not x < y => x > y


know:
	forall x, y R => x = y <=> not x > y, not x < y
	forall x, y R => x > y <=> not x <= y
	forall x, y R => x < y <=> not x >= y
	forall x, y R => x != y <=> x > y or x < y
	forall x, y R => x >= y <=> x = y or x > y
	forall x, y R => x <= y <=> x = y or x < y

# Logical operator equivalences
know:
	forall x, y R => not x < y <=> x >= y
	forall x, y R => not x > y <=> x <= y
	forall x, y R => not x <= y <=> x > y
	forall x, y R => not x >= y <=> x < y

prop mul_cancel_cond(a, b, c R):
    a * c = b * c
    c != 0

prop div_cancel_cond(a, b, c R):
    a / c = b / c
    c != 0

know imply cancel(a, b, c R):
    or:
        a + c = b + c
        a - c = b - c
        $mul_cancel_cond(a, b, c)
        $div_cancel_cond(a, b, c)
    =>:
        a = b

prop mul_cancel_general_cond(a, b, c, d R):
    a * c = b * d
    c != 0

prop div_cancel_general_cond(a, b, c, d R):
    a / c = b / d
    c != 0


know imply cancel_general(a, b, c, d R):
    c = d
    or:
        a + c = b + d
        a - c = b - d
        $mul_cancel_general_cond(a, b, c, d)
        $div_cancel_general_cond(a, b, c, d)
    =>:
        a = b

know imply product_is_0_then_at_least_one_factor_is_0(a, b R):
	a * b = 0
	=>:
		or:
			a = 0
			b = 0

know:
	forall a, b, c, e, f, g R:
		a = e
		b + c = f + g
		=>:
			a + b + c = e + f + g

	forall a, b, c, e, f, g R:
		a = e
		b * c = f * g
		=>:
			a * b * c = e * f * g
			
	forall a, b, c, d R : b + c = d => a + b + c = a + d

know:
	forall a, b R:
		a > 0
		b > 0
		=>:
			a + b > 0
			a * b > 0
			a /b > 0
	forall a, b R:
		a < 0
		b > 0
		=>:
			a * b < 0
			b * a < 0
			a / b < 0
			b / a < 0

know:
	forall x, y R: x >= 0, y >= 0 => x + y >= 0
	forall x R: x < 0 => -x > 0
	forall x R: x > 0 => -x < 0
	forall x R: x >= 0 => -x <= 0
	forall x R: x <= 0 => -x >= 0
	forall x R: x != 0 => -x != 0
	forall x R: x != 0 => -x != 0

know:
	forall x R, y R: x > 0, y > 0 => x^y > 0

let fn log(x, y R) R:
	dom:
		x > 0
		x != 1
		y > 0

# TODO: 这里的 y ^ z 可能不满足^的定义域的要求
know:
	forall x, y, z R: x > 0, x != 1, y > 0, z > 0 => log(x, y^z) = z * log(x, y)
	forall x, y, z R: x > 0, x != 1, y > 0, z > 0 => log(x, y * z) = log(x, y) + log(x, z)
	forall x R: x > 0, x != 1 => log(x, x) = 1

let pi R # pi is the ratio of the circumference of a circle to its diameter

know:
	forall x, y, z R: x + y = z => x = z - y, y = z - x
	forall x, y, z R: x - y = z => x = z + y, y = x - z
	forall x, y, z R: x = y + z => x - y = z, x - z = y
	forall x, y, z R: x = y - z => x - y = -z, x + z = y, z + x = y

know:
	forall a, b, c, d R: b != 0, d != 0, a / b = c / d => a * d = b * c

know:
    forall a, b, c, d R:
        b != 0
		c != 0
        d != 0
        =>:
            (a / b) / (c / d) = (a * d) / (b * c)

know forall a, b, c, d R: c != 0, a = (b / c) * d => a * c = b * d
know forall a, b, c, d R: c != 0, a = d * (b / c) => a * c = d * b
know forall x, y, z R: z != 0, x = y / z => x * z = y

let fn range(x Z, y Z) set:
	=>:
		range(x, y) = {self Z: self >= x, self < y}

let fn closed_range(x Z, y Z) set:
	=>:
		closed_range(x, y) = {self Z: self >= x, self <= y}

"""
know:
	forall x, y set:
		=>:
			x = y
		<=>:
			forall t x:
				t $in y
			forall t y:
				t $in x
"""

know:
	forall x, y R: x < y => x - y < 0
	forall x, y R: x > y => x - y > 0
	forall x, y R: x <= y => x - y <= 0
	forall x, y R: x >= y => x - y >= 0
	forall x, y R: x = y => x - y = 0
	forall x, y R: x != y => x - y != 0

know imply larger_is_transitive(x, y, z R):
	x > y
	y > z
	=>:
		x > z

know imply less_equal_add_cancel(x, y, z R):
	x + z <= y + z
	=>:
		x <= y

know imply less_equal_minus_cancel(x, y, z R):
	x - z <= y - z
	=>:
		x <= y

know imply less_add_cancel(x, y, z R):
	x + z < y + z
	=>:
		x < y

know imply less_minus_cancel(x, y, z R):
	x - z < y - z
	=>:
		x < y

know imply greater_add_cancel(x, y, z R):
	x + z > y + z
	=>:
		x > y

know imply greater_minus_cancel(x, y, z R):
	x - z > y - z
	=>:
		x > y

know imply greater_equal_add_cancel(x, y, z R):
	x + z >= y + z
	=>:
		x >= y

know imply greater_equal_minus_cancel(x, y, z R):
	x - z >= y - z
	=>:
		x >= y

know imply greater_equal_mul_pos_cancel(x, y, z R):
	z > 0
	x * z >= y * z
	=>:
		x >= y

know imply greater_equal_div_pos_cancel(x, y, z R):
	z > 0
	x / z >= y / z
	=>:
		x >= y

know imply greater_div_pos_cancel(x, y, z R):
	z > 0
	x / z > y / z
	=>:
		x > y

know imply less_div_pos_cancel(x, y, z R):
	z > 0
	x / z < y / z
	=>:
		x < y

know imply less_equal_div_pos_cancel(x, y, z R):
	z > 0
	x / z <= y / z
	=>:
		x <= y

know imply less_div_neg_cancel(x, y, z R):
	z < 0
	x / z < y / z
	=>:
		x > y

know imply less_equal_div_neg_cancel(x, y, z R):
	z < 0
	x / z <= y / z
	=>:
		x >= y

know imply greater_equal_mul_neg_cancel(x, y, z R):
	z < 0
	x / z >= y / z
	=>:
		x <= y

know imply greater_equal_div_neg_cancel(x, y, z R):
	z < 0
	x / z > y / z
	=>:
		x < y

know imply less_equal_mul_neg_cancel(x, y, z R):
	z < 0
	x * z <= y * z
	=>:
		x >= y

know imply larger_equal_mul_neg_cancel(x, y, z R):
	z < 0
	x * z >= y * z
	=>:
		x <= y

know imply less_mul_neg_cancel(x, y, z R):
	z < 0
	x * z < y * z
	=>:
		x > y

know imply greater_mul_neg_cancel(x, y, z R):
	z < 0
	x * z > y * z
	=>:
		x < y

know imply greater_than_pow_cancel(x, y, z R):
	z > 0
	x > 0
	y > 0
	x ^ z > y ^ z
	=>:
		x > y

know imply greater_equal_pow_cancel(x, y, z R):
	z > 0
	x > 0
	y > 0
	x ^ z >= y ^ z
	=>:
		x >= y

know imply less_pow_cancel(x, y, z R):
	z > 0
	x > 0
	y > 0
	x ^ z < y ^ z
	=>:
		x < y

know imply less_equal_pow_cancel(x, y, z R):
	z > 0
	x > 0
	y > 0
	x ^ z <= y ^ z

know:
	forall x, y R: x > 0, y > 0 => x * y > 0
	forall x, y R: x > 0, y < 0 => x * y < 0
	forall x, y R: x < 0, y < 0 => x * y > 0
	forall x, y R: x < 0, y > 0 => x * y < 0
	forall x, y R: x >= 0, y >= 0 => x * y >= 0
	forall x, y R: x >= 0, y <= 0 => x * y <= 0
	forall x, y R: x <= 0, y <= 0 => x * y >= 0
	forall x, y R: x <= 0, y >= 0 => x * y <= 0
	forall x, y R => x > y <=> not x <= y
	forall x, y R => x < y <=> not x >= y
	forall x, y R => x <= y <=> not x > y
	forall x, y R => x >= y <=> not x < y

let fn pow(x R, y R) R:
	dom:
		x >= 0
		or:
			x != 0
			y != 0

know forall b N: b >= 0

know forall a, b R: a ^ 2 = b => a = sqrt(b) or a = -sqrt(b), a = pow(b, 1/2) or a = -pow(b, 1/2)
know forall a, b R: a ^ 2 = b, a >= 0 => a = sqrt(b), a = pow(b, 1/2)

know forall x, y, z Z: z != 0 => (x + y) % z = (x % z + y % z) % z, (x * y) % z = (x % z * y % z) % z, (x - y) % z = (x % z - y % z) % z

let fn negate(x R) R:
	negate(x) = -x
	negate(x) + x = 0
	x + negate(x) = 0

know forall x set: not x $in x

prop subset_of(x, y set):
	forall z x:
		=>:
			z $in y

prop is_superset_of(A, B set):
	forall x B: x $in A

"""
let fn intersect(x, y set) set:
	forall z x:
		z $in y
		=>:
			z $in intersect(x, y)
	forall z y:
		z $in x
		=>:
			z $in intersect(x, y)
"""


"""
let fn union(x, y set) set:
	forall z x:
		z $in union(x, y)
	forall z y:
		z $in union(x, y)
"""


prop sets_are_equal(x, y set):
	forall a x => a $in y
	forall a y => a $in x
know:
	forall x, y set: x = y <=> x $sets_are_equal y

know forall a, x, b, y R: a != 0, a * x + b = y => x = (y - b) / a

know:
	forall x R, y Z: x != 0, y % 2 = 0 => x ^ y > 0
	forall x R, y Z: y % 2 = 0, y != 0 => x ^ y >= 0

know:
	forall x, y, z R: x <= y => x + z <= y + z, x - z <= y - z, z + x <= z + y
	forall x, y, z R: x <= y, z > 0 => x * z <= y * z, x / z <= y / z, z * x <= z * y
	forall x, y, z R: x >= y => x + z >= y + z, x - z >= y - z, z + x >= z + y
	forall x, y, z R: x >= y, z > 0 => x * z >= y * z, x / z >= y / z, z * x >= z * y
	forall x, y, z R: x > y => x + z > y + z, x - z > y - z, z + x > z + y
	forall x, y, z R: x > y, z > 0 => x * z > y * z, x / z > y / z, z * x > z * y
	forall x, y, z R: x < y => x + z < y + z, x - z < y - z, z + x < z + y
	forall x, y, z R: x < y, z > 0 => x * z < y * z, x / z < y / z, z * x < z * y

know forall x, y R: y > 0, x >= 0 => x / y >= 0
know:
	forall x, y R: x >= y <=> x - y >= 0
	forall x, y R: x > y <=> x - y > 0
	forall x, y R: x <= y <=> x - y <= 0
	forall x, y R: x < y <=> x - y < 0

know:
	forall x, y R: y >= 0 => x + y >= x, y + x >= x, x <= x + y, x <= y + x
	forall x, y R: abs(x + y) <= abs(x) + abs(y)
	forall x, y R: x > 0, y > 1 => x * y > x, y * x > x
	forall x, y, z R: x > y, z < 0 => x * z < y * z
	forall x, y R: x > y => not x <= y, not x = y, not x < y
	forall x, y R: x < y => not x >= y, not x = y, not x > y

know imply subset_of_finite_set_is_finite_set(x set, y finite_set):
	x $subset_of y
	=>:
		$is_finite_set(x)
		count(x) <= count(y)

prop is_cart(x set)

prop is_tuple(x set)

"""
let fn proj(x set, i N_pos) set:
	dom:
		$is_cart(x)
		i <= dim(x)

let fn dim(x set) N_pos:
	dom:
		$is_cart(x)
"""

# ∏_{a in I} A_a (Cartesian product)
prop is_cart_prod(s set)
"""
let fn index_set_of_cart_prod(s set) set:
	dom:
		$is_cart_prod(s)
"""
		
# let fn cart_prod(index_set set, family fn (index_set) set) set

know:
	forall x, y R:
		x >= 0
		or:
			x != 0
			y != 0
		=>:
			x ^ (y + 1) = (x ^ y) * x

	forall x N_pos: x >= 0, x > 0, x != 0, x >= 1, not x < 1, not x < 0

"""
let fn inverse_image_set(X set, Y set, f fn(X)Y, U set) set:
    U $subset_of Y
    =>:
        inverse_image_set(X, Y, f, U) = {self X: f(self) $in U}

let fn difference(x, y set) set
know:
	forall x, y set, z x:
		not z $in y
		<=>:
			z $in difference(x, y)

know imply item_in_difference(x, y set, z set):
	z $in difference(x, y)
	=>:
		not z $in y
		z $in x

"""


know:
	forall a, b, c, d R: b > 0, d > 0 => a / b > c / d <=> a * d > b * c
	forall a, b, c, d R: b > 0, d > 0 => a / b < c / d <=> a * d < b * c
	forall a, b, c, d R: b > 0, d > 0 => a / b >= c / d <=> a * d >= b * c
	forall a, b, c, d R: b > 0, d > 0 => a / b <= c / d <=> a * d <= b * c
	forall a, b, c, d R: b != 0, d != 0 => a / b = c / d <=> a * d = b * c
	forall a, b, c, d R: b < 0, d < 0 => a / b > c / d <=> a * d < b * c
	forall a, b, c, d R: b < 0, d < 0 => a / b < c / d <=> a * d > b * c
	forall a, b, c, d R: b < 0, d < 0 => a / b >= c / d <=> a * d <= b * c
	forall a, b, c, d R: b < 0, d < 0 => a / b <= c / d <=> a * d >= b * c
	forall a, b, c, d R: b > 0, d < 0 => a / b > c / d <=> a * d < b * c
	forall a, b, c, d R: b > 0, d < 0 => a / b < c / d <=> a * d > b * c
	forall a, b, c, d R: b > 0, d < 0 => a / b >= c / d <=> a * d <= b * c
	forall a, b, c, d R: b > 0, d < 0 => a / b <= c / d <=> a * d >= b * c
	forall a, b, c, d R: b < 0, d > 0 => a / b > c / d <=> a * d < b * c
	forall a, b, c, d R: b < 0, d > 0 => a / b < c / d <=> a * d > b * c
	forall a, b, c, d R: b < 0, d > 0 => a / b >= c / d <=> a * d <= b * c
	forall a, b, c, d R: b < 0, d > 0 => a / b <= c / d <=> a * d >= b * c

prop not_both_zero(a, b R):
	a != 0 or b != 0
	a ^ 2 + b ^ 2 != 0
	a^2 + b^2 > 0

know:
	forall a R: a != 0 => a ^ 2 > 0, a ^ 2 != 0, a * a > 0
	forall a, b R: a ^ 2 + b ^ 2 >= 0

know forall x, y R: x > y or x <= y, x < y or x >= y, x = y or x != y

prop equal_tuple(x, y set, dim N_pos):
	$is_tuple(x)
	$is_tuple(y)
	dim(x) = dim
	dim(y) = dim
	<=>:
		x = y

know:
	forall x, y set:
		$is_tuple(x)
		$is_tuple(y)
		dim(x) = dim(y)
		forall i N_pos: i <= dim(x) => x[i] = y[i]
		=>:
			x = y

"""
let fn power_set(x set) set
know forall x set, y power_set(x): y $subset_of x, forall t y => t $in x
know forall x, y set: x $subset_of y => x $in power_set(y)
"""

know forall x, y set => x = y <=> x $subset_of y, y $subset_of x

know forall x R: abs(x) >= 0
know forall x R: x >= 0 => sqrt(x) = 0 <=> x = 0
			
know:
	forall a, b, c R: a > 0, a * b > c => b > c / a
	forall a, b R, c N_pos: a > 0, b > 0, a > b => a^c > b^c
	forall a, b R: a != b <=> a - b != 0
	forall a, b R: a > 0, b >= 0 => a + b > 0

know:
	not $is_nonempty_set({})
	forall x set: {} $subset_of x
	forall x set: not x $in {}
	forall x set: x != {} <=> $is_nonempty_set(x)

prop equal_set(x set, y set)

know:
	forall x R: x > 0 => 1 / x > 0
	forall x R, y R: x > 0, y > 0 => x > y <=> 1 / x < 1 / y
	forall x, y, a, b R: x != 0, y != 0 x / y = a / b <=> y / x = b / a

know: 
	$is_nonempty_set(R)
	$is_nonempty_set(N)
	$is_nonempty_set(N_pos)
	$is_nonempty_set(Z)
	$is_nonempty_set(Q)
	$is_nonempty_set(Q_pos)
	$is_nonempty_set(Q_neg)
	$is_nonempty_set(Z_neg)
	$is_nonempty_set(R_pos)
	$is_nonempty_set(R_neg)

# TODO: builtin instead of fn
# 一个东西在cup，则怎么怎么样；一个东西满足了cup的性质，则怎么怎么样
"""
# cap
know imply item_in_cap(z set, x set, y cap(x)):
	forall t x:
		z $in t


prop is_item_in_cap(z set, x set, y set):


# set_minus
know imply item_in_set_minus(x, y set, z set_minus(x, y)):
	z $in x
	not z $in y

# set symmetric difference
know imply item_in_set_diff(x, y set):
	forall z set_diff(x, y):
		z $in x
		=>:
			not z $in y
	forall z set_diff(x, y):
		z $in y
		=>:
			not z $in x
"""
		
# TODO: builtin instead of fn
"""
let fn choice(x set) fn(x) cup(x)
know imply axiom_of_choice(x set):
	forall y x:
		choice(x)(y) $in y
"""

know:
	forall x, y R: x < y => $is_nonempty_set(range(x, y)), $is_nonempty_set(closed_range(x, y))

know:
	forall x finite_set: count(x) > 0 => $is_nonempty_set(x)

know forall x set: x \union x = x, x \intersect x = x

know:
	forall x R: x > 0 <=> x $in R_pos
	forall x R: x < 0 <=> x $in R_neg
	forall x Z: x < 0 <=> x $in Z_neg
	forall x Q: x < 0 <=> x $in Q_neg
	forall x Q: x > 0 <=> x $in Q_pos

# density of Q, R
know:
	forall x, y R: x < y => exist z Q st z $in {t R: x < t, t < y}
	forall x, y R: x < y => exist z R st z $in {t R: x < t, t < y}

prop superset_of(x, y set):
	forall z y:
		z $in x

know:
	forall x R: exist y R st y > x
	forall x R: exist y R st y < x
	forall x R: exist y R st y >= x
	forall x R: exist y R st y <= x

	forall x R: exist y N_pos st y > x
	forall x R: exist y Z_neg st y < x
	forall x R: exist y N_pos st y >= x
	forall x R: exist y Z_neg st y <= x

know:
	forall x, y R: x < y => {t R: x < t, t < y} $is_nonempty_set
	forall x, y R: x < y => {t R: x <= t, t <= y} $is_nonempty_set
	forall x, y R: x < y => {t R: x <= t, t < y} $is_nonempty_set
	forall x, y R: x < y => {t R: x < t, t <= y} $is_nonempty_set

## Set theory super functions: cup, cap, union, intersect, power set, set minus, set diff

### cup

# check item in cup
know imply check_item_in_cup(x set, x_item x, cup_x_item x_item):
	cup_x_item $in cup(x)

# when item in cup, it has properties
know forall x set, cup_x_item cup(x) => exist x_item x st cup_x_item $in x_item
	
### cap

# check item in cap
know:
	forall x set, item set:
		forall x_item x:
			item $in x_item
		=>:
			item $in cap(x)

# when item in cap, it has properties
know imply item_in_cap_implies(x set, item cap(x)):
	forall x_item x:
		item $in x_item

### union

# check item in union
know:
	forall item, x, y set: item $in x or item $in y => item $in union(x, y)

# when item in union, it has properties
know imply item_in_union_implies(z set, x, y set):
	z $in union(x, y)
	=>:
		z $in x or z $in y

# Properties of union
know:
	forall x, y set: $is_nonempty_set(x) or $is_nonempty_set(y) => $is_nonempty_set(union(x, y))

### intersect

# check item in intersect
know:
	forall item, x, y set: item $in x, item $in y => item $in intersect(x, y)

# when item in intersect, it has properties
know imply item_in_intersect_implies(z set, x, y set):
	z $in intersect(x, y)
	=>:
		z $in x
		z $in y

### power set

# check item in power_set
know:
	forall x set, y set:
		y $subset_of x
		=>:
			y $in power_set(x)

# when item in power set, it has properties
know:
	forall x set, y power_set(x):
		y $subset_of x

### set minus

# check item in set minus
know:
	forall item, x, y set:
		item $in x
		not item $in y
		=>:
			item $in set_minus(x, y)

# when item in set minus, it has properties
know imply item_in_set_minus_implies(x, y set, item set_minus(x, y)):
	item $in x
	not item $in y

### set diff

know:
	forall x, y set:
		set_diff(x, y) = set_minus(x, y) \union set_minus(y, x)

## End of set theory

## Function Related

prop is_injective_fn(X set, Y set, f fn(X)Y):
	forall x1, x2 X:
		x1 != x2
		=>:
			f(x1) != f(x2)

know:
	forall X set, Y set, f fn(X)Y:
		forall x1, x2 X:
			f(x1) = f(x2)
			=>:
				x1 = x2
		=>:
			$is_injective_fn(X, Y, f)

prop is_surjective_fn(X set, Y set, f fn(X)Y):
	forall y Y:
		exist x X st f(x) = y

prop is_bijective_fn(X set, Y set, f fn(X)Y):
	$is_injective_fn(X, Y, f)
	$is_surjective_fn(X, Y, f)
	
know imply is_injective_fn_to_finite_set_implies(X set, Y finite_set, f fn(X)Y):
	$is_injective_fn(X, Y, f)
	=>:
		$is_finite_set(Y)
		count(X) <= count(Y)

prop not_equal_set(x set, y set)

know imply is_nonempty_with_item(x, z set):
	z $in x
	=>:
		$is_nonempty_set(x)
		
# 和序数，有限有关的事实
know:
	forall x finite_set: count(x) > 0 <=> not $is_nonempty_set(x)
	forall left, right Z, x set: left <= right, x = range(left, right) => count(x) = right - left
	forall left, right Z, x set: left <= right, x = closed_range(left, right) => count(x) = right - left + 1
	forall left, right Z => $is_finite_set(range(left, right)), $is_finite_set(closed_range(left, right))
	forall x finite_set: count(x) $in N,  0 <= count(x)
	forall x, y finite_set: count(x) <= count(y) <=> x $subset_of y

# ZFC
# 1. Axiom of extensionality: two sets are equal if and only if they have the same elements. We use keyword equal_set for this. Equivalently, we can use = for this because there is no difference between them in Litex (any object in Litex is a set). But it's better to use equal_set for this to emphasize we are using the definition of equality of sets.

# 2. Axiom of regularity: every non-empty set has an element that is disjoint from the set
prop disjoint_from(x set, y set):
	forall z x:
		not z $in y
	forall z y:
		not z $in x

know forall x nonempty_set: exist y x st y $disjoint_from x

# 3. Axiom schema of specification: we can construct a set from a given set and a property. We use keyword {x parent_set: $p1(..), $p2(..), ...} for this.

# 4. Axiom of pairing: we can construct a set from two given sets. We use {x, y} for this.

# 5. Axiom of union: we can construct a set from a given set of sets. We use keyword union(x) and cup(x) for this.

# 6. Axiom schema of replacement: the image of a set under any definable function will also fall inside a set

# 7. Axiom of infinity: there exists an infinite set
prop axiom_of_infinity(x set):
	{} $in x
	forall y x:
		union(y, {y}) $in x

know exist x set st $axiom_of_infinity(x)

# 8. Axiom of power set: for any set, there exists a set of all subsets of the set. We use keyword power_set for this.

# 9. Axiom of choice: for any set of non-empty sets, there exists a choice function that chooses an element from each set. We use keyword choice for this.

### choice

# choice(S, s) chooses an element from s, where s is an element of S
# For any set S (which is a set of sets), if each element of S is a non-empty set,
# then for any s in S, choice(S, s) is in s.
know:
	forall S set, s S:
		forall x S:
			$is_nonempty_set(x)
		=>:
			choice(S, s) $in s

# End of ZFC

# 常见的和自然数相关的结论
prop is_max_in(i set, s set):
	s $subset_of R
	i $in s
	<=>:
		forall j s:
			j <= i

prop is_min_in(i set, s set):
	s $subset_of R
	i $in s
	<=>:
		forall j s:
			i <= j

know:
	forall s power_set(R):
		$is_finite_set(s)
		=>:
			exist i s st $is_max_in(i, s)
			exist i s st $is_min_in(i, s)

know forall x Z: x >= 0 => x $in N
`
