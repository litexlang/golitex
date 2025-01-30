package parser

import (
	"fmt"
	"testing"
)

func TestParseFc(t *testing.T) {
	strings := []string{
		"f[G, B](a, b)[C, D](c, d)",
		"f[G, B](a, b).g[G, B].t(a, b)",
	}

	for _, s := range strings {
		tokens, err := tokenizeString(s)
		if err != nil {
			t.Fatal(err)
		}
		parser := Parser{0, *tokens}
		fc, err := parser.parseFc()
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(fc)
	}
}

func TestParseBracketVarTypePair(t *testing.T) {
	tokens := []string{"[", "g", "Group", ",", "v", "Group", "]"}
	parser := Parser{0, tokens}
	fc, err := parser.parseBracketedVarTypePair()
	if err != nil {
		t.Fatal(err)
	}

	fmt.Println(fc)
}

func TestParseBuiltinFnRetValue(t *testing.T) {
	strings := []string{
		"-1 + 2 ^ 3 * 4 / 5 + 6 + f[G, B](a, b).g[G, B].t(a, b) * f[G, B](a, b)[C, D](c, d)",
		"f[G, B](a, b).g[G, B].t(a, b) + 1.2",
		"1.2 + 1.3 * 14.2",
		"f[G, B](a, b)[C, D](c, d) + 6 * 5",
		"-1 + 2 ^ 3 * 4 / 5 + 6",
	}

	for _, s := range strings {
		tokens, err := tokenizeString(s)
		if err != nil {
			t.Fatal(err)
		}
		parser := Parser{0, *tokens}

		fc, err := parser.parseBuiltinFnRetValue()

		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(fc)
	}
}
