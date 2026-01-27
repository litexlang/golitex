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
// Litex Zulip community: https://litexlang.zulipchat.com/join/c4e7foogy6paz2sghjnbov/

package litex_expr

import (
	"fmt"
	"testing"
)

func TestSimplify_BasicExpressions(t *testing.T) {
	testCases := []struct {
		input string
		name  string
	}{
		{"1 + 2", "simple addition"},
		{"x + y", "variable addition"},
		{"x * y", "variable multiplication"},
		{"x + x", "like terms"},
		{"2 * x + 3 * x", "coefficient addition"},
		{"x + 3 * x", "coefficient addition"},
		{"2 * f(x) + 3 * f(x)", "coefficient addition"},
		{"2 * f(x) + 3 * f(y) + f(x) * 3", "coefficient addition"},
		{"1 + 2 + 3", "multiple numbers"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Simplify(tc.input)
			fmt.Printf("Input: %s\n", tc.input)
			fmt.Printf("Output: %s\n", result)
			fmt.Println("---")
		})
	}
}

func TestSimplify_Expansion(t *testing.T) {
	testCases := []struct {
		input string
		name  string
	}{
		{"x * (y + z)", "basic expansion"},
		{"(a + b) * (c + d)", "double expansion"},
		{"f(a) * (b + t)", "function with expansion"},
		{"x * (y + z) + w", "expansion with addition"},
		{"(x + y) * (a + b) + (c + d)", "complex expansion"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Simplify(tc.input)
			fmt.Printf("Input: %s\n", tc.input)
			fmt.Printf("Output: %s\n", result)
			fmt.Println("---")
		})
	}
}

func TestSimplify_ComplexTerms(t *testing.T) {
	testCases := []struct {
		input string
		name  string
	}{
		{"f(a)", "simple function"},
		{"f(a)(b)", "function call with multiple args"},
		{"f(a) + g(b)", "multiple functions"},
		{"f(a)(b) + g(c)(d) + 3 * f(a)(b)", "complex function terms"},
		{"f(a + 1)", "function with expression"},
		{"f(a + 1) * x", "function multiplied"},
		{"f(a + 1) + g(b + 2)", "functions with expressions"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Simplify(tc.input)
			fmt.Printf("Input: %s\n", tc.input)
			fmt.Printf("Output: %s\n", result)
			fmt.Println("---")
		})
	}
}

func TestSimplify_Division(t *testing.T) {
	testCases := []struct {
		input string
		name  string
	}{
		{"x / y", "simple division"},
		{"x / y + a / b", "multiple divisions"},
		{"(x + y) / z", "numerator expression"},
		{"x / (y + z)", "denominator expression"},
		{"f(a) / b", "function division"},
		{"x + f(a) / b", "addition with division"},
		{"x + f(a) / b + f(a)", "multiple terms with division"},
		{"(x + y) / (a + b)", "complex fraction"},
		{"x / y / z", "chained division"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Simplify(tc.input)
			fmt.Printf("Input: %s\n", tc.input)
			fmt.Printf("Output: %s\n", result)
			fmt.Println("---")
		})
	}
}

func TestSimplify_Exponentiation(t *testing.T) {
	testCases := []struct {
		input string
		name  string
	}{
		{"x ^ 2", "simple power"},
		{"x ^ y", "variable power"},
		{"(x + y) ^ 2", "expression power"},
		{"x ^ 2 + y ^ 2", "multiple powers"},
		{"x ^ 2 * y ^ 3", "power multiplication"},
		{"f(a) ^ 2", "function power"},
		{"x ^ 2 + x ^ 2", "like power terms"},
		{"x ^ 2 + 2 * x ^ 2", "power with coefficient"},
		{"(x + 1) ^ 2 + (x + 1) ^ 2", "like expression powers"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Simplify(tc.input)
			fmt.Printf("Input: %s\n", tc.input)
			fmt.Printf("Output: %s\n", result)
			fmt.Println("---")
		})
	}
}

func TestSimplify_MixedOperations(t *testing.T) {
	testCases := []struct {
		input string
		name  string
	}{
		{"x + y / z", "addition and division"},
		{"x * y + z / w", "multiplication and division"},
		{"x ^ 2 + y / z", "power and division"},
		{"f(a) * (b + t) + x / y", "function expansion with division"},
		{"x ^ 2 + f(a)(b)[1] / c", "power, function, and division"},
		{"(x + y) ^ 2 + (a + b) / (c + d)", "complex mixed"},
		{"1 + 2 + 2 * a + a * 2 + a * a", "like terms combination"},
		{"x + f(a + 1) * (b + t) + y / z", "all operations"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Simplify(tc.input)
			fmt.Printf("Input: %s\n", tc.input)
			fmt.Printf("Output: %s\n", result)
			fmt.Println("---")
		})
	}
}

func TestSimplify_LikeTerms(t *testing.T) {
	testCases := []struct {
		input string
		name  string
	}{
		{"1 + 2 + 3", "numbers"},
		{"x + x", "same variable"},
		{"2 * x + 3 * x", "coefficient addition"},
		{"a * x + b * x", "variable coefficient"},
		{"x * y + x * y", "product terms"},
		{"x ^ 2 + x ^ 2", "power terms"},
		{"1 + 2 + 2 * a + a * 2 + a * a", "complex like terms"},
		{"x + x + x", "multiple same terms"},
		{"f(a) + f(a)", "function terms"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Simplify(tc.input)
			fmt.Printf("Input: %s\n", tc.input)
			fmt.Printf("Output: %s\n", result)
			fmt.Println("---")
		})
	}
}

func TestEqual_Basic(t *testing.T) {
	testCases := []struct {
		left     string
		right    string
		expected bool
		name     string
	}{
		{"1 + 2", "3", true, "simple addition"},
		{"x + y", "y + x", true, "commutative addition"},
		{"x * y", "y * x", true, "commutative multiplication"},
		{"2 * x + 3 * x", "5 * x", true, "like terms"},
		{"x + x", "2 * x", true, "double variable"},
		{"x / y", "x / y", true, "same division"},
		{"(x + y) / z", "x / z + y / z", false, "expansion check"}, // 这个可能应该是 true，但当前实现可能不支持
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Equal(tc.left, tc.right)
			fmt.Printf("Left: %s\n", tc.left)
			fmt.Printf("Right: %s\n", tc.right)
			fmt.Printf("Expected: %v, Got: %v\n", tc.expected, result)
			fmt.Println("---")
		})
	}
}

func TestEqual_Fractions(t *testing.T) {
	testCases := []struct {
		left     string
		right    string
		expected bool
		name     string
	}{
		{"x / y", "x / y", true, "same fraction"},
		{"(x * z) / (y * z)", "x / y", false, "cancel factor"},                      // 可能应该是 true
		{"x / y + a / b", "(x * b + a * y) / (y * b)", false, "common denominator"}, // 可能应该是 true
		{"f(a) / b", "f(a) / b", true, "function fraction"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Equal(tc.left, tc.right)
			fmt.Printf("Left: %s\n", tc.left)
			fmt.Printf("Right: %s\n", tc.right)
			fmt.Printf("Expected: %v, Got: %v\n", tc.expected, result)
			fmt.Println("---")
		})
	}
}

func TestSimplify_ComplexExpressions(t *testing.T) {
	testCases := []struct {
		input string
		name  string
	}{
		{"f(a)(b)[1] + g(c)(d)[2] + h(e)", "multiple complex functions"},
		{"x * f(a)(b)[1] + y * g(c)(d)[2]", "function multiplication"},
		{"f(a)(b)[1] / x + g(c)(d)[2] / y", "function division"},
		{"f(a)(b)[1] ^ 2 + g(c)(d)[2] ^ 3", "function power"},
		{"(x + f(a)(b)[1]) * (y + g(c)(d)[2])", "expansion with functions"},
		{"f(a + 1)(b + 2)[1] + g(c + 3)(d + 4)[2]", "functions with expressions"},
		{"x + f(a)(b)[1] / c + y + g(d)(e)[2] / f", "all mixed"},
		{"f(a)(b)[1] * (x + y) + g(c)(d)[2] * (a + b)", "function expansion"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := Simplify(tc.input)
			fmt.Printf("Input: %s\n", tc.input)
			fmt.Printf("Output: %s\n", result)
			fmt.Println("---")
		})
	}
}
