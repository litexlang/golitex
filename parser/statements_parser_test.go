package parser

import (
	"fmt"
	"testing"
)

func TestForallStmt(t *testing.T) {
	tokenized1, err := tokenizeString("forall [G Group] g1 G, g2 G:")
	if err != nil {
		t.Fatal(err)
	}
	tokenized2, err := tokenizeString("$f[G, B](a, b)[C, D](c, d)")
	if err != nil {
		t.Fatal(err)
	}

	block :=
		TokenStmt{
			Parser{0, *tokenized1},
			[]TokenStmt{
				TokenStmt{
					Parser{0, *tokenized2},
					[]TokenStmt{},
				},
				TokenStmt{
					Parser{0, *tokenized2},
					[]TokenStmt{},
				},
			},
		}

	cur, err := block.parseForallStmt()

	if err != nil {
		t.Fatal(err)
	}

	fmt.Sprintf("%v", cur)
}
