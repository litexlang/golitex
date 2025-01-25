package parser

import (
	"fmt"
	"testing"
)

func TestParseFc(t *testing.T) {
	tokens := []string{"f", "[", "G", ",", "B", "]", "(", "a", ",", "b", ")", "[", "G", ",", "B", "]", "(", "a", ",", "b", ")"}
	parser := Parser{0, tokens}
	fc, err := parser.parseFc()
	if err != nil {
		t.Fatal(err)
	}
	fmt.Println(fc)
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
