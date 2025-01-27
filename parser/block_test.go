package parser

import (
	"fmt"
	"testing"
)

func TestLexer(t *testing.T) {
	block, err := ParseFile("../examples/concept.litex")
	if err != nil {
		t.Fatalf(err.Error())
	}

	for _, block := range block.body {
		fmt.Println(block.String())
	}
}

// Test given string
func TestLexerFromString(t *testing.T) {
	content := `
def add(a, b):
    return a + b
`
	blocks, err := getTopLevelStmtSlice(content)
	if err != nil {
		t.Fatalf(err.Error())
	}

	for _, block := range blocks.body {
		fmt.Println(block.String())
	}

	// Test invalid syntax
	_, err = getTopLevelStmtSlice(content)
	if err != nil {
		t.Fatalf("Expected error for invalid syntax")
	}
}
