package parser

import (
	"fmt"
	"testing"
)

func TestLexer(t *testing.T) {
	blocks, err := ParseFile("../test/add.py")
	if err != nil {
		t.Fatalf(err.Error())
	}

	for _, block := range blocks {
		fmt.Println(block)
	}
}

// Test given string
func TestLexerFromString(t *testing.T) {
	content := `
def add(a, b):
    return a + b
`
	blocks, err := ParseString(content)
	if err != nil {
		t.Fatalf(err.Error())
	}

	for _, block := range blocks {
		fmt.Println(block)
	}

	// Test invalid syntax
	_, err = ParseString(content)
	if err != nil {
		t.Fatalf("Expected error for invalid syntax")
	}
}
