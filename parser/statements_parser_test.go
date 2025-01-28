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

func parserTester(code string) (*[]Stmt, error) {
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := getTopLevelStmtSlice(code)
	if err != nil {
		return nil, err
	}

	blocks := []tokenBlock{}
	for _, strBlock := range slice.body {
		block, err := TokenizeStmtBlock(&strBlock)
		if err != nil {
			return nil, err
		}
		blocks = append(blocks, *block)
	}

	ret := []Stmt{}
	for _, block := range blocks {
		cur, err := block.ParseStmt()
		if err != nil {
			return nil, err
		}
		ret = append(ret, cur)
		fmt.Printf("%v\n", cur)
	}

	return &ret, nil
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
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
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
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
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
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefFnStmt(t *testing.T) {
	code := `
fn P[G Group, G2 Group](g G, g2 G2) fn [G Group, G2 Group](g G, g2 G2):
	if:
    	$f[G, B](g.g1, g2.g2)
	then:
		$f[G, B](g.g1, g2.g2)

$f[G, B](g.g1, g2.g2)
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestFactStatements(t *testing.T) {
	code := `
$f[G, B](g.g1, g2.g2)

forall [G Group] x g:
	$f[G, B](g.g1, g2.g2)

`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestParseDefTypeStmt(t *testing.T) {
	code :=
		`
type G Group

type G Group:
	var_member:
		var 1 G
		fn f[G Group, G2 Group](x G, y G) G
		property f[G Group, G2 Group](x G, y G)

	then:
		$p[G, G2](x, y)

type G Group:
	$p[G, G2](x, y)
`

	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestParseFactStmt(t *testing.T) {
	code :=
		`
$p[G, G2](x, y)

forall [G Group, G2 Group] g G, g2 G2:
    $p[G, G2](x, y)

forall [G Group, G2 Group] g g, g2 g2:
	if:
		$p[G, G2](x, y)
	then:
	    $p[G, G2](x, y)
		forall [G Group, G2 Group] g g, g2 g2:
			if:
				$p[G, G2](x, y)
			then:
				$p[G, G2](x, y)
		
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestParseVarStmt(t *testing.T) {
	code :=
		`
var g G
var g G:
    $p[G, G2](x, y)
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestParseClaimStmt(t *testing.T) {

	code :=
		`
claim :
	$p[G, G2](x, y)

	proof:
		$p[G, G2](x, y)

claim :
	forall [G Group, G2 Group] g g, g2 g2:
		if:
			$p[G, G2](x, y)
		then:
			$p[G, G2](x, y)
			forall [G Group, G2 Group] g g, g2 g2:
				if:
					$p[G, G2](x, y)
				then:
					$p[G, G2](x, y)

	proof:
		$p[G, G2](x, y)

claim:
	$p[G, G2](x, y)
	$p[G, G2](x, y)
		
	proof:
		$p[G, G2](x, y)
		

`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestParseDefAliasStmt(t *testing.T) {
	code :=
		`
alias a p[G, G2](x, y)
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestKnowStmt(t *testing.T) {
	code :=
		`
know:
	$p[G, G2](x, y)
	forall [G Group, G2 Group] g g, g2 g2:
		if:
			$p[G, G2](x, y)
		then:
			$p[G, G2](x, y)
			forall [G Group, G2 Group] g g, g2 g2:
				if:
					$p[G, G2](x, y)
				then:
					$p[G, G2](x, y)
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}
