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

	tokenizedIf, err := tokenizeString("if:")
	if err != nil {
		t.Fatal(err)
	}

	tokenizedThen, err := tokenizeString("then:")
	if err != nil {
		t.Fatal(err)
	}

	block2 :=
		TokenStmt{
			Parser{0, *tokenized1},
			[]TokenStmt{
				TokenStmt{
					Parser{0, *tokenizedIf},
					[]TokenStmt{
						TokenStmt{
							Parser{0, *tokenized2},
							[]TokenStmt{},
						},
					},
				},
				TokenStmt{
					Parser{0, *tokenizedThen},
					[]TokenStmt{
						TokenStmt{
							Parser{0, *tokenized2},
							[]TokenStmt{},
						},
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
						},
					},
				},
			},
		}

	cur, err = block2.parseForallStmt()
	if err != nil {
		t.Fatal(err)
	}
	fmt.Sprintf("%v", cur)
}

func TestDefPropertyStmt(t *testing.T) {
	tokenized1, err := tokenizeString("property ha [G Group] (g1 G, g2 G):")
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

	cur, err := block.parseDefPropertyStmt()

	tokenizedIf, err := tokenizeString("if:")
	if err != nil {
		t.Fatal(err)
	}

	tokenizedThen, err := tokenizeString("then:")
	if err != nil {
		t.Fatal(err)
	}

	block2 :=
		TokenStmt{
			Parser{0, *tokenized1},
			[]TokenStmt{
				TokenStmt{
					Parser{0, *tokenizedIf},
					[]TokenStmt{
						TokenStmt{
							Parser{0, *tokenized2},
							[]TokenStmt{},
						},
					},
				},
				TokenStmt{
					Parser{0, *tokenizedThen},
					[]TokenStmt{
						TokenStmt{
							Parser{0, *tokenized2},
							[]TokenStmt{},
						},
					},
				},
			}}

	cur, err = block2.parseDefPropertyStmt()
	if err != nil {
		t.Fatal(err)
	}

	fmt.Sprintf("%v", cur)
}
