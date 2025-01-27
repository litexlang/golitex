package parser

import (
	"fmt"
	"strings"
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
		tokenBlock{
			Parser{0, *tokenized1},
			[]tokenBlock{
				{
					Parser{0, *tokenized2},
					[]tokenBlock{},
				},
				{
					Parser{0, *tokenized2},
					[]tokenBlock{},
				},
			},
		}

	cur, err := block.parseForallStmt()

	if err != nil {
		t.Fatal(err)
	}
	fmt.Printf("%v", cur)

	tokenizedIf, err := tokenizeString("if:")
	if err != nil {
		t.Fatal(err)
	}

	tokenizedThen, err := tokenizeString("then:")
	if err != nil {
		t.Fatal(err)
	}

	block2 :=
		tokenBlock{
			Parser{0, *tokenized1},
			[]tokenBlock{
				{
					Parser{0, *tokenizedIf},
					[]tokenBlock{
						{
							Parser{0, *tokenized2},
							[]tokenBlock{},
						},
					},
				},
				{
					Parser{0, *tokenizedThen},
					[]tokenBlock{
						{
							Parser{0, *tokenized2},
							[]tokenBlock{},
						},
						{
							Parser{0, *tokenized1},
							[]tokenBlock{
								{
									Parser{0, *tokenized2},
									[]tokenBlock{},
								},
								{
									Parser{0, *tokenized2},
									[]tokenBlock{},
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
	fmt.Printf("%v", cur)
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
		tokenBlock{
			Parser{0, *tokenized1},
			[]tokenBlock{
				{
					Parser{0, *tokenized2},
					[]tokenBlock{},
				},
				{
					Parser{0, *tokenized2},
					[]tokenBlock{},
				},
			},
		}

	cur, err := block.parseDefPropertyStmt()
	if err != nil {
		t.Fatal(err)
	}
	fmt.Printf("%v", cur)

	tokenizedIf, err := tokenizeString("if:")
	if err != nil {
		t.Fatal(err)
	}

	tokenizedThen, err := tokenizeString("then:")
	if err != nil {
		t.Fatal(err)
	}

	block2 :=
		tokenBlock{
			Parser{0, *tokenized1},
			[]tokenBlock{
				{
					Parser{0, *tokenizedIf},
					[]tokenBlock{
						{
							Parser{0, *tokenized2},
							[]tokenBlock{},
						},
					},
				},
				{
					Parser{0, *tokenizedThen},
					[]tokenBlock{
						{
							Parser{0, *tokenized2},
							[]tokenBlock{},
						},
					},
				},
			}}

	cur, err = block2.parseDefPropertyStmt()
	if err != nil {
		t.Fatal(err)
	}

	fmt.Printf("%v", cur)
}

func TestDefConceptStmt(t *testing.T) {
	code := `concept G Group:
	inherit:
		set
		group
	
	type_member:
		var 1 G
		fn f[G Group, G2 Group](x G, y G) G
		property f[G Group, G2 Group](x G, y G)

	var_member:
		var 1 G
		fn f[G Group, G2 Group](x G, y G) G
		property f[G Group, G2 Group](x G, y G)

	then:
		$p[G, G2](x, y)
		
`
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := getTopLevelStmtSlice(code)
	if err != nil {
		t.Fatal(err)
	}

	blocks := []tokenBlock{}
	for _, strBlock := range slice.body {
		block, err := TokenizeStmtBlock(&strBlock)
		if err != nil {
			t.Fatal(err)
		}
		blocks = append(blocks, *block)
	}

	for _, block := range blocks {
		cur, err := block.ParseStmt()
		if err != nil {
			t.Fatal(err)
		}
		fmt.Printf("%v\n", cur)
	}
}

func TestParseLocalStmt(t *testing.T) {
	code :=
		`
local:
	concept G Group:
		inherit:
			set
			group
		
		type_member:
			var 1 G
			fn f[G Group, G2 Group](x G, y G) G
			property f[G Group, G2 Group](x G, y G)

		var_member:
			var 1 G
			fn f[G Group, G2 Group](x G, y G) G
			property f[G Group, G2 Group](x G, y G)

		then:
			$p[G, G2](x, y)

	local:
		concept G Group:
			inherit:
				set
				group
			
			type_member:
				var 1 G
				fn f[G Group, G2 Group](x G, y G) G
				property f[G Group, G2 Group](x G, y G)

			var_member:
				var 1 G
				fn f[G Group, G2 Group](x G, y G) G
				property f[G Group, G2 Group](x G, y G)

			then:
				$p[G, G2](x, y)

`
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := getTopLevelStmtSlice(code)
	if err != nil {
		t.Fatal(err)
	}

	blocks := []tokenBlock{}
	for _, strBlock := range slice.body {
		block, err := TokenizeStmtBlock(&strBlock)
		if err != nil {
			t.Fatal(err)
		}
		blocks = append(blocks, *block)
	}

	for _, block := range blocks {
		cur, err := block.ParseStmt()
		if err != nil {
			t.Fatal(err)
		}
		fmt.Printf("%v\n", cur)
	}

}

func TestDefPropertyStmt2(t *testing.T) {
	code := `
property P[G Group, G2 Group](g G, g2 G2):
	if:
    	$f[G, B](g.g1, g2.g2)
	then:
		$f[G, B](g.g1, g2.g2)

property P[G Group, G2 Group](g G, g2 G2):
	$f[G, B](g.g1, g2.g2)

`
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := getTopLevelStmtSlice(code)
	if err != nil {
		t.Fatal(err)
	}

	blocks := []tokenBlock{}
	for _, strBlock := range slice.body {
		block, err := TokenizeStmtBlock(&strBlock)
		if err != nil {
			t.Fatal(err)
		}
		blocks = append(blocks, *block)
	}

	for _, block := range blocks {
		cur, err := block.ParseStmt()
		if err != nil {
			t.Fatal(err)
		}
		fmt.Printf("%v\n", cur)
	}
}

func TestDefFnStmt(t *testing.T) {
	code := `
fn P[G Group, G2 Group](g G, g2 G2) fn [G Group, G2 Group](g G, g2 G2):
	if:
    	$f[G, B](g.g1, g2.g2)
	then:
		$f[G, B](g.g1, g2.g2)
`
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := getTopLevelStmtSlice(code)
	if err != nil {
		t.Fatal(err)
	}

	blocks := []tokenBlock{}
	for _, strBlock := range slice.body {
		block, err := TokenizeStmtBlock(&strBlock)
		if err != nil {
			t.Fatal(err)
		}
		blocks = append(blocks, *block)
	}

	for _, block := range blocks {
		cur, err := block.ParseStmt()
		if err != nil {
			t.Fatal(err)
		}
		fmt.Printf("%v\n", cur)
	}
}
