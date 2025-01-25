package parser

import (
	"fmt"
	"testing"
)

// Test function for parseFuncPtyStmt
func TestParseFuncPtyStmt(t *testing.T) {
	tokens := []string{"$", "<", "(", "1", ",", "2", ")"}
	tokenStmt := TokenStmt{Parser{0, tokens}, nil}
	fmt.Println(tokenStmt)
}

func TestParsePtyStmt(t *testing.T) {
	tokens := []string{"$", "<", "(", "1", ",", "2", ")"}
	tokenStmt := TokenStmt{Parser{0, tokens}, nil}
	fmt.Println(tokenStmt)
}

func TestParseIfStmt(t *testing.T) {
	tokens := []string{"if", "[", "G", "Group", "]", "(", "v", "G", ")", ":"}
	tokens2 := []string{"$", "<", "(", "1", ",", "2", ")"}
	tokenStmt2 := TokenStmt{Parser{0, tokens2}, nil}

	body := []TokenStmt{tokenStmt2}
	tokenStmt := TokenStmt{Parser{0, tokens}, &body}
	fmt.Println(fmt.Sprintf("%v", tokenStmt))
}
