package parser

import (
	"fmt"
	"testing"
)

func TestParseTypeVarPairBracketWithoutFacts(t *testing.T) {
	tokens := []string{"[", "g", "Group", ",", "v", "Group", "]"}
	start := 0
	bracket, err := parseTypeVarPairBracket(&tokens, &start)
	if err != nil {
		t.Fatal(err)
	}
	pairs := bracket.pairs
	if len(pairs) != 2 || (pairs)[0].Var != "g" || (pairs)[0].Type != "Group" || (pairs)[1].Var != "v" || (pairs)[1].Type != "Group" {
		t.Error("Expected pairs: [{g Group}, {v Group}], but got: ", pairs)
	}

	if start != len(tokens) {
		t.Error("Expected end index: ", len(tokens), ", but got: ", start)
	}
}

func TestParseTypeVarPairBraceWithoutFacts(t *testing.T) {
	tokens := []string{"(", "g", "Group", ",", "v", "Group", ")"}

	start := 0
	bracket, err := parseTypeVarPairBrace(&tokens, &start)
	if err != nil {
		t.Fatal(err)
	}
	pairs := bracket.pairs
	if len(pairs) != 2 || (pairs)[0].Var != "g" || (pairs)[0].Type != "Group" || (pairs)[1].Var != "v" || (pairs)[1].Type != "Group" {
		t.Error("Expected pairs: [{g Group}, {v Group}], but got: ", pairs)
	}
}

func TestParseFc(t *testing.T) {
	tokens := []string{"f", "[", "G", ",", "B", "]", "(", "a", ",", "b", ")", "[", "G", ",", "B", "]", "(", "a", ",", "b", ")"}
	start := 0
	fc, err := parseFc(&tokens, &start)
	if err != nil {
		t.Fatal(err)
	}
	fmt.Println(fc)
}

func TestParseBracketVarTypePair(t *testing.T) {
	tokens := []string{"[", "g", "Group", ",", "v", "Group", "]"}
	start := 0
	bracket, err := parseBracketedVarTypePair(&tokens, &start)
	if err != nil {
		t.Fatal(err)
	}
	pairs := bracket.pairs
	if len(pairs) != 2 || (pairs)[0].Var != "g" || (pairs)[0].Type != "Group" || (pairs)[1].Var != "v" || (pairs)[1].Type != "Group" {
		t.Error("Expected pairs: [{g Group}, {v Group}], but got: ", pairs)
	}
}
