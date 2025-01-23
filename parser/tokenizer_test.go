package parser

import (
	"fmt"
	"testing"
)

func TestSplitString(t *testing.T) {
	input := []string{"concept [G Group[G Set](v G)]:"}
	for _, s := range input {
		tokens, err := splitString(s)

		if err != nil {
			t.Fatalf("Error splitting string: %s", err.Error())
			continue
		}

		for _, token := range tokens {
			fmt.Println(token)
		}
	}
}

func TestParseStrStmtBlock(t *testing.T) {
	input := SourceCodeStmtBlock{
		Header: "concept [G Group[G Set](v G)]:",
		Body: []SourceCodeStmtBlock{
			{
				Header: "concept [G Set](v G):",
				Body: []SourceCodeStmtBlock{
					{
						Header: "concept [v G](v G):",
						Body:   []SourceCodeStmtBlock{},
					},
				},
			},
		},
	}

	parsedBlock, err := TokenizeStmtBlock(&input)
	if err != nil {
		t.Fatalf(err.Error())
	}

	fmt.Println(parsedBlock)
}
