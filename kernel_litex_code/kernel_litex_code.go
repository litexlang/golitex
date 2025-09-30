// Copyright 2024 Jiachen Shen.
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
prop last_two_objects_are_equal(x, y, y2 obj):
	y = y2

know @larger_is_transitive(x, y, z R):
	x > y
	y > z
	=>:
		x > z

exist_prop a in_set st exist_obj_not_in_left_set_but_in_right_set(not_in_set, in_set set):
	not a $in not_in_set

know forall x2, y2 R: x2 != 0, y2 != 0 => x2 * y2 != 0

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

fn sqrt(z R) R:
	z >= 0
	=>:
		sqrt(z) ^ 2 = z
		sqrt(z) >= 0

know forall z R: z > 0 => sqrt(z) > 0

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

know @less_equal_add_cancel(x, y, z R):
	x + z <= y + z
	=>:
		x <= y

know @less_equal_minus_cancel(x, y, z R):
	x - z <= y - z
	=>:
		x <= y

know @less_add_cancel(x, y, z R):
	x + z < y + z
	=>:
		x < y

know @less_minus_cancel(x, y, z R):
	x - z < y - z
	=>:
		x < y

know @greater_add_cancel(x, y, z R):
	x + z > y + z
	=>:
		x > y

know @greater_minus_cancel(x, y, z R):
	x - z > y - z
	=>:
		x > y

know @greater_equal_add_cancel(x, y, z R):
	x + z >= y + z
	=>:
		x >= y

know @greater_equal_minus_cancel(x, y, z R):
	x - z >= y - z
	=>:
		x >= y

know @greater_equal_mul_pos_cancel(x, y, z R):
	z > 0
	x * z >= y * z
	=>:
		x >= y

know @greater_equal_div_pos_cancel(x, y, z R):
	z > 0
	x / z >= y / z
	=>:
		x >= y

know @greater_div_pos_cancel(x, y, z R):
	z > 0
	x / z > y / z
	=>:
		x > y

know @less_div_pos_cancel(x, y, z R):
	z > 0
	x / z < y / z
	=>:
		x < y

know @less_equal_div_pos_cancel(x, y, z R):
	z > 0
	x / z <= y / z
	=>:
		x <= y

know @less_div_neg_cancel(x, y, z R):
	z < 0
	x / z < y / z
	=>:
		x > y

know @less_equal_div_neg_cancel(x, y, z R):
	z < 0
	x / z <= y / z
	=>:
		x >= y

know @greater_equal_mul_neg_cancel(x, y, z R):
	z < 0
	x / z >= y / z
	=>:
		x <= y

know @greater_equal_div_neg_cancel(x, y, z R):
	z < 0
	x / z > y / z
	=>:
		x < y

know @less_equal_mul_neg_cancel(x, y, z R):
	z < 0
	x * z <= y * z
	=>:
		x >= y

know @larger_equal_mul_neg_cancel(x, y, z R):
	z < 0
	x * z >= y * z
	=>:
		x <= y

know @less_mul_neg_cancel(x, y, z R):
	z < 0
	x * z < y * z
	=>:
		x > y

know @greater_mul_neg_cancel(x, y, z R):
	z < 0
	x * z > y * z
	=>:
		x < y

know @greater_than_pow_cancel(x, y, z R):
	z > 0
	x > 0
	y > 0
	x ^ z > y ^ z
	=>:
		x > y

know @greater_equal_pow_cancel(x, y, z R):
	z > 0
	x > 0
	y > 0
	x ^ z >= y ^ z
	=>:
		x >= y

know @less_pow_cancel(x, y, z R):
	z > 0
	x > 0
	y > 0
	x ^ z < y ^ z
	=>:
		x < y

know @less_equal_pow_cancel(x, y, z R):
	z > 0
	x > 0
	y > 0
	x ^ z <= y ^ z

fn abs(x R) R
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

know forall x R: or(x > 0, x < 0) => x != 0

# 必须要有，否则不能说明有限集合的子集还是有限集合
know @finite_set_subset_is_finite_set(s1 finite_set, s2 set):
	forall x s2:
		x $in s1
	=>:
		s2 $in finite_set

know forall x N: x != 0 => x > 0

know forall x, y R: x > 0, y > 0 => x * y > 0

know forall x, y R: x > 0, y > 0 => x ^ y $in R, x ^ y > 0, x * y > 0

know forall x Z => x $in Q, x $in R, x $in C

know forall x N_pos => x $in N, x >= 1, x > 0, x $in Q, x $in R, x $in C

fn_template seq(s set):
	fn (n N) s

fn_template finite_seq(s set, n N_pos):
    fn (x N) s:
    	dom:
        	x < n

fn finite_seq_sum(n N_pos, a finite_seq(R, n), k N) R:
    dom:
        k < n

know:
    forall n N_pos, a finite_seq(R, n), k N: k < n - 1 => finite_seq_sum(n, a, k+1) = finite_seq_sum(n, a, k) + a(k+1)
    forall n N_pos, a finite_seq(R, n) => finite_seq_sum(n, a, 0) = a(0)

fn finite_seq_product(n N_pos, a finite_seq(R, n), k N) R:
    dom:
        k < n

know:
    forall n N_pos, a finite_seq(R, n), k N: k < n - 1 => finite_seq_product(n, a, k+1) = finite_seq_product(n, a, k) * a(k+1)
    forall n N_pos, a finite_seq(R, n) => finite_seq_product(n, a, 0) = a(0)

know:
	$exist_in(N)
	$exist_in(N_pos)
	$exist_in(Z)
	$exist_in(Q)
	$exist_in(R)
	$exist_in(C)
	forall x N_pos:
		x > 0

have set fn range(x N) := y N:
    y < x

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

know @subtraction_preserves_inequality_with_positive_term(a R, b R, c R):
    a < b - c
    c > 0
    =>:
        a < b

know forall x , y R: y > 0 => x + y > x

know forall x, y R: not x > y => x <= y
know forall x, y R: not x < y => x >= y
know forall x, y R: not x >= y => x < y
know forall x, y R: not x <= y => x > y
know forall x, y R: not x = y, not x > y => x < y
know forall x, y R: not x = y, not x < y => x > y

know:
	forall x R: x = x => not x > x, not x < x
	forall x R: x > x => not x = x, not x < x
	forall x R: x < x => not x = x, not x > x
	forall x R: x >= x => not x < x
	forall x R: x <= x => not x > x
	forall x R: x != x => x > x, x < x

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

know @cancel(a, b, c R):
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


know @cancel_general(a, b, c, d R):
    c = d
    or:
        a + c = b + d
        a - c = b - d
        $mul_cancel_general_cond(a, b, c, d)
        $div_cancel_general_cond(a, b, c, d)
    =>:
        a = b

# TODO: 之后把这个移除kernel_lib而是做成像set一样内置的东西
know:
	$exist_in(nonempty_set)
	forall x nonempty_set:
		x $in set
		$exist_in(x)

know @product_is_0_then_at_least_one_factor_is_0(a, b R):
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

fn log(x, y R) R:
	dom:
		x > 0
		x != 1
		y > 0

know:
	forall x, y, z R: x > 0, y > 0, z > 0 => log(x, y^z) = z * log(x, y)
	forall x, y, z R: x > 0, y > 0, z > 0 => log(x, y * z) = log(x, y) + log(x, z)
	forall x R: x > 0 => log(x, x) = 1

let pi R # pi is the ratio of the circumference of a circle to its diameter

know:
	forall x, y, z R: x + y = z => x = z - y, y = z - x
	forall x, y, z R: x - y = z => x = z + y, y = x - z
	forall x, y, z R: x = y + z => x - y = z, x - z = y
	forall x, y, z R: x = y - z => x - y = -z, x + z = y

know:
	forall a, b, c, d R: b != 0, d != 0, a / b = c / d => a * d = b * c
`
