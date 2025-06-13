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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_num

import (
	"fmt"
	"strings"
	"testing"
)

func TestExpandExpression(t *testing.T) {
	// expr := "3*[x] + [f(x)]*[y/2] + ([x] + [y]) * [z] + 5*[x]"
	expr := "1 + 2 * 4 + [t(x)] + 9 + 4 * [F(t)]"
	fmt.Println("Input:", expr)
	poly := ParseAndExpandPolynomial(expr)

	var parts []string
	for _, t := range poly {
		parts = append(parts, t.String())
	}
	fmt.Println("Expanded:", strings.Join(parts, " + "))

}

func TestCombineFractions(t *testing.T) {
	exprs := []string{
		"1/2*h + t*a/b*k - c/d*h",
		"1*a + f * b",
		"1/2*h + t*f(a/2)",
		"(f(a))(b/2) + (f(a))(b/2)",
		"a*b/c",
		"a*b/c + d*e/f",
		"a*b/c + d*e/f + g*h/i",
		"a*b/c + d*e/f + g*h/i + j*k/l",
		"a*b/c + d*e/f + g*h/i + j*k/l + m*n/o",
		"a*b/c + d*e/f + g*h/i + j*k/l + m*n/o + p*q/r",
		"a*b/c + d*e/f + g*h/i + j*k/l + m*n/o + p*q/r + s*t/u",
	}
	for _, expr := range exprs {
		numerator, denominator, err := combineFractions(expr)
		if err != nil {
			t.Fatalf("Error combining fractions: %v", err)
		}
		fmt.Println("Numerator:", numerator)
		fmt.Println("Denominator:", denominator)
	}
}
