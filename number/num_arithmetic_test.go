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
				fmt.Printf("  Term %d: CoEff=%g, Vars=%v\n", i+1, term.CoEff, term.Vars)
			}
			fmt.Println("---")
		})
	}
}
