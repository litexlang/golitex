package parser

import (
	"fmt"
	"testing"
)

// Test function for parseFuncPtyStmt
func TestParseFuncPtyStmt(t *testing.T) {
	tokens := []string{"$", "<", "(", "1", ",", "2", ")"}
	tokenStmt := TokenStmt{tokens, []TokenStmt{}}
	stmt, err := parseFuncPtyStmt(&tokenStmt)
	if err != nil {
		t.Error(err)
	}

	// print stmt
	fmt.Println(fmt.Sprintf("%v", stmt))
}

func TestParsePtyStmt(t *testing.T) {
	tokens := []string{"$", "<", "(", "1", ",", "2", ")"}
	tokenStmt := TokenStmt{tokens, []TokenStmt{}}
	stmt, err := ParseStmt(&tokenStmt)
	if err != nil {
		t.Error(err)
	}
	fmt.Println(fmt.Sprintf("%v", stmt))
}

func TestParseIfStmt(t *testing.T) {
	tokens := []string{"if", "[", "G", "Group", "]", "(", "v", "G", ")", ":"}
	tokens2 := []string{"$", "<", "(", "1", ",", "2", ")"}
	tokenStmt2 := TokenStmt{tokens2, []TokenStmt{}}

	tokenStmt := TokenStmt{tokens, []TokenStmt{tokenStmt2}}
	stmt, err := ParseStmt(&tokenStmt)
	if err != nil {
		t.Error(err)
	}
	fmt.Println(fmt.Sprintf("%v", stmt))
}
