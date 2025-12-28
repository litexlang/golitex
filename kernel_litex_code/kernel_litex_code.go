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
exist_prop a in_set st exist_obj_not_in_left_set_but_in_right_set(not_in_set, in_set set):
	not a $in not_in_set

know forall x2, y2 R: x2 != 0, y2 != 0 => x2 * y2 != 0

exist_prop x Z, y N_pos st Q_in_frac(q Q):
	x / y = q
	x = y * q
	x = q * y
	y > 0

exist_prop x Z, y N_pos st rational_number_representation_in_fraction(q Q):
	<=>:
		x / y = q
		x = y * q
		x = q * y
		y > 0

exist_prop x N_pos, y N_pos st rational_positive_number_representation_in_fraction(q Q):
	q > 0
	<=>:
		x / y = q
		x = y * q
		x = q * y
		x > 0
		y > 0

exist_prop x Z, y N_pos st rational_negative_number_representation_in_fraction(q Q):
	q < 0
	<=>:
		x / y = q
		x = y * q
		x = q * y
		x < 0

know forall q Q => $rational_number_representation_in_fraction(q)
know forall q Q: q > 0 => $rational_positive_number_representation_in_fraction(q)
know forall q Q: q < 0 => $rational_negative_number_representation_in_fraction(q)

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

# TODO: 已经放到 Std/Int/main.lit 中
know:
	forall x, y Z, z N:
		z != 0
		=>:
			(x + y) % z = (x % z + y % z) % z

# TODO: 已经放到 Std/Int/main.lit 中
know forall x, y Z, z N: z !=0, x % z = 0 => (x * y) % z = 0

# TODO: 已经放到 Std/Int/main.lit 中
know forall x, z N: z != 0, x < z => x % z = x

# TODO: 已经放到 Std/Int/main.lit 中
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
		$is_a_finite_set(s2)

know forall x N: x != 0 => x > 0

know forall x, y R: x > 0, y > 0 => x ^ y $in R, x ^ y > 0, x * y > 0

know forall x Z => x $in Q, x $in R

know forall x N_pos => x $in N, x >= 1, x > 0, x $in Q, x $in R
know forall x Z: x > 0 => x $in N_pos
know forall x Z: x <= 0 => not x $in N_pos

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
` + InequalityFacts

var InequalityFacts = `
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

exist_prop s set st there_exists_infinite_set() :
    <=>:
        not $is_a_finite_set(s)

know $there_exists_infinite_set()

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

know imply item_in_intersect(z set, x, y set):
	z $in intersect(x, y)
	=>:
		z $in x
		z $in y

"""
let fn union(x, y set) set:
	forall z x:
		z $in union(x, y)
	forall z y:
		z $in union(x, y)
"""

know imply item_in_union(z set, x, y set):
	z $in union(x, y)
	=>:
		z $in x or z $in y

let fn complement(x, y set) set:
	dom:
		x $subset_of y
	=>:
		forall z y:
			not z $in x
			=>:
				z $in complement(x, y)

know imply item_in_complement(z set, x, y set):
	x $subset_of y
	z $in complement(x, y)
	=>:
		z $in y
		not z $in x

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
		$is_a_finite_set(x)
		count(x) <= count(y)

prop is_cart(x set)

prop is_tuple(x set)

let fn proj(x set, i N_pos) set:
	dom:
		$is_cart(x)
		i <= dim(x)

let fn dim(x set) N_pos:
	dom:
		$is_cart(x)

# ∏_{a in I} A_a (Cartesian product)
prop is_cart_prod(s set)
let fn index_set_of_cart_prod(s set) set:
	dom:
		$is_cart_prod(s)
		
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

let fn power_set(x set) set
know:
	forall x set, y power_set(x):
		y $subset_of x
	forall x set, y set:
		y $subset_of x
		=>:
			y $in power_set(x)

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

let fn subsets(x set) set
know forall x set, y subsets(x): y $subset_of x, forall t y => t $in x
know forall x, y set: x $subset_of y => x $in subsets(y)

know forall x, y set => x = y <=> x $subset_of y, y $subset_of x

know forall x R: abs(x) >= 0
know forall x R: x >= 0 => sqrt(x) = 0 <=> x = 0

exist_prop x X st has_preimage(X, Y set, f fn(X)Y, y Y):
	f(x) = y

prop is_injective_fn(X set, Y set, f fn(X)Y):
	forall x1, x2 X:
		x1 != x2
		=>:
			f(x1) != f(x2)

prop is_surjective_fn(X set, Y set, f fn(X)Y):
	forall y Y:
		$has_preimage(X, Y, f, y)

prop is_bijective_fn(X set, Y set, f fn(X)Y):
	$is_injective_fn(X, Y, f)
	$is_surjective_fn(X, Y, f)

# 如何证明集合是有限集合
exist_prop f fn(X)Y st exist_one_to_one_fn_to_finite_set(X finite_set, Y set):
	$is_bijective_fn(X, Y, f)
			
know:
	forall a, b, c R: a > 0, a * b > c => b > c / a
	forall a, b R, c N_pos: a > 0, b > 0, a > b => a^c > b^c
	forall a, b R: a != b <=> a - b != 0
	forall a, b R: a > 0, b >= 0 => a + b > 0

know:
	not $is_a_nonempty_set({})
	forall x set: {} $subset_of x
	forall x set: not x $in {}
	forall x set: x != {} <=> $is_a_nonempty_set(x)

prop equal_set(x set, y set)

know:
	forall x R: x > 0 => 1 / x > 0
	forall x R, y R: x > 0, y > 0 => x > y <=> 1 / x < 1 / y
	forall x, y, a, b R: x != 0, y != 0 x / y = a / b <=> y / x = b / a

know: 
	$is_a_nonempty_set(R)
	$is_a_nonempty_set(N)
	$is_a_nonempty_set(N_pos)
	$is_a_nonempty_set(Z)
	$is_a_nonempty_set(Q)
	$is_a_finite_set(R)
	$is_a_finite_set(N)
	$is_a_finite_set(N_pos)
	$is_a_finite_set(Z)
	$is_a_finite_set(Q)

# TODO: builtin instead of exist_prop
exist_prop y x st axiom_of_regularity(x nonempty_set):
    forall z y: not z $in x
    forall z x: not z $in y

know forall x nonempty_set: $axiom_of_regularity(x)

# TODO: builtin instead of fn
let fn cup(x set) set
know imply cup_contains_all_items(x set, y x):
	forall z y:
		z $in cup(x)
exist_prop y x st cup_witness_item(x set, z cup(x)):
	z $in y

# TODO: builtin instead of exist_prop
exist_prop x s1 st exist_preimage(s1, s2 set, y s2, f fn(s1)s2):
    f(x) = y

let fn image_set(s1, s2 set, f fn(s1)s2) set

know:
    forall s1, s2 set, f fn(s1)s2, y image_set(s1, s2, f):
        $exist_preimage(s1, s2, y, f)

    forall s1, s2 set, f fn(s1)s2, y s2:
        $exist_preimage(s1, s2, y, f)
        =>:
            y $in image_set(s1, s2, f)

	forall s1, s2 set, f fn(s1)s2:
		image_set(s1, s2, f) $subset_of s2

# TODO: builtin instead of fn
let fn choice(x set) fn(x) cup(x)
know imply axiom_of_choice(x set):
	forall y x:
		choice(x)(y) $in y

# Axiom of infinity
exist_prop x set st axiom_of_infinity():
	{} $in x
	forall y x:
		union(y, {y}) $in x

know:
	forall x, y R: x < y => $is_a_nonempty_set(range(x, y)), $is_a_nonempty_set(closed_range(x, y))

know:
	forall x finite_set: count(x) > 0 => $is_a_nonempty_set(x)

know forall x set: x \union x = x, x \intersect x = x

`
