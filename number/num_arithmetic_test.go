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

package litex_num

import (
	"fmt"
	"testing"
)

func TestPolynomialPrint(t *testing.T) {
	testCases := []struct {
		input    string
		expected string
	}{
		{"[x]*[x]*[y]", "[x^2]*[y]"},
		{"[x]*[x]*[x]*[y]*[y]", "[x^3]*[y^2]"},
		{"[x]*[y]*[x]*[z]", "[x^2]*[y]*[z]"},
		{"2*[x]*[x] + 3*[y]", "2*[x^2] + 3*[y]"},
	}

	for _, tc := range testCases {
		t.Run(tc.input, func(t *testing.T) {
			poly := ParseAndExpandPolynomial(tc.input)
			result := ExpandPolynomial_ReturnStr(tc.input)
			fmt.Printf("Input: %s\n", tc.input)
			fmt.Printf("Result: %s\n", result)
			fmt.Printf("Polynomial terms:\n")
			for i, term := range poly {
				fmt.Printf("  Term %d: CoEff=%s, Vars=%s\n", i+1, term.CoEff, term.Vars)
			}
			fmt.Println("---")
		})
	}
}
