package parser

import (
	"fmt"
	"testing"
)

// Test function for parseFuncPtyStmt
func TestParseFuncPtyStmt(t *testing.T) {
	tokens := []string{"$", "<", "(", "1", ",", "2", ")"}
	tokenStmt := TokenStmt{tokens, nil}
	fmt.Println(tokenStmt)
}

func TestParsePtyStmt(t *testing.T) {
	tokens := []string{"$", "<", "(", "1", ",", "2", ")"}
	tokenStmt := TokenStmt{tokens, nil}
	fmt.Println(tokenStmt)
}

func TestParseIfStmt(t *testing.T) {
	tokens := []string{"if", "[", "G", "Group", "]", "(", "v", "G", ")", ":"}
	tokens2 := []string{"$", "<", "(", "1", ",", "2", ")"}
	tokenStmt2 := TokenStmt{tokens2, nil}

	body := []TokenStmt{tokenStmt2}
	tokenStmt := TokenStmt{tokens, &body}
	fmt.Println(fmt.Sprintf("%v", tokenStmt))
}
