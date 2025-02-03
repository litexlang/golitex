package parser

import (
	"fmt"
	"strings"
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

func TestSplitString(t *testing.T) {
	input := []string{"concept [G Group[G Set](v G)]:"}
	for _, s := range input {
		tokens, err := tokenizeString(s)

		if err != nil {
			t.Fatalf("Error splitting string: %s", err.Error())
			continue
		}

		for _, token := range *tokens {
			fmt.Println(token)
		}
	}
}

func TestParseStrStmtBlock(t *testing.T) {
	subBody := []StrBlock{
		{
			Header: "concept [v G](v G):",
			Body:   nil,
		},
	}
	body := []StrBlock{
		{
			Header: "concept [G Set](v G):",
			Body:   subBody,
		},
	}
	input := StrBlock{
		Header: "concept [G Group[G Set](v G)]:",
		Body:   body,
	}

	parsedBlock, err := TokenizeStmtBlock(&input)
	if err != nil {
		t.Fatalf(err.Error())
	}

	fmt.Println(parsedBlock)
}

func TestFileTokenize(t *testing.T) {
	filePath := "../examples/concept.litex"
	block, err := ParseFile(filePath)
	if err != nil {
		t.Fatalf(err.Error())
	}

	for _, stmt := range block.body {
		parsedBlock, err := TokenizeStmtBlock(&stmt)
		if err != nil {
			t.Fatalf(err.Error())
		}

		fmt.Println(parsedBlock.String())
	}
}

func TestParseFc(t *testing.T) {
	strings := []string{
		"f[G, B](a, b)[C, D](c, d)",
		"f[G, B](a, b).g[G, B].t(a, b)",
	}

	for _, s := range strings {
		tokens, err := tokenizeString(s)
		if err != nil {
			t.Fatal(err)
		}
		parser := Parser{0, *tokens}
		fc, err := parser.parseFcAtom()
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(fc)
	}
}

func TestParseBracketVarTypePair(t *testing.T) {
	tokens := []string{"[", "g", "Group", ",", "v", "Group", "]"}
	parser := Parser{0, tokens}
	fc, err := parser.parseBracketedTypeConceptPairArray()
	if err != nil {
		t.Fatal(err)
	}

	fmt.Println(fc)
}

func TestParseBuiltinFnRetValue(t *testing.T) {
	strings := []string{
		"-1 + 2 ^ 3 * 4 / 5 + 6 + f[G, B](a, b).g[G, B].t(a, b) * f[G, B](a, b)[C, D](c, d)",
		"f[G, B](a, b).g[G, B].t(a, b) + 1.2",
		"1.2 + 1.3 * 14.2",
		"f[G, B](a, b)[C, D](c, d) + 6 * 5",
		"-1 + 2 ^ 3 * 4 / 5 + 6",
	}

	for _, s := range strings {
		tokens, err := tokenizeString(s)
		if err != nil {
			t.Fatal(err)
		}
		parser := Parser{0, *tokens}

		fc, err := parser.parseFcExpr()

		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(fc)
	}
}

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

	member:
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

		member:
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

			member:
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
	member:
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

func TestParseDefuseStmt(t *testing.T) {
	code :=
		`
use a p[G, G2](x, y)
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

func TestExistStmt(t *testing.T) {
	code :=
		`
exist P[G Group, G2 Group](g1 G, g2 G2):
	if:
		$p[G, G2](x, y)
		forall [G Group, G2 Group] g g, g2 g2:
			if:
				$p[G, G2](x, y)
			then:
				$p[G, G2](x, y)

	member:
	    var 1 G
		fn f[G Group, G2 Group](x G, y G) G

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

func TestHaveStmt(t *testing.T) {
	code :=
		`
have $P[G , G2 ](g1 , g2 ):
	g1, g2
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestVarDeclStmt(t *testing.T) {
	code :=
		`
var g1 G, g2 G

var a G,  b G:
	$p[g](a)
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestMemberStmt(t *testing.T) {
	code :=
		`
member [G Group](g G) 		var 1 G:
	$p[g](a)
member [G Group](g G) 		fn f[G Group, G2 Group](x G, y G) G:
    $p[g](a)
member [G Group](g G) 		property f[G Group, G2 Group](x G, y G)
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestConceptMemberStmt(t *testing.T) {
	code :=
		`
type_member [G Group]		var 1 G:
	$p[g](a)
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestRelationalFactStmt(t *testing.T) {
	code :=
		`
p[g](a) + 2 < (2 + 3) * 10 + 4 < 100
10 = p[g](a) = p[g](a)
`
	statements, err := parseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestIsStmt(t *testing.T) {
	// 	3 is p[g](a)
	// $p[g](a)

	code :=
		`
( p[g](a) + 2 ) is q
1 * ( p[g](a) + 2 ) is q

`
	statements, err := parseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestTypedFuncPtyStmt(t *testing.T) {
	code :=
		`
$$[G Group](x fn [x g](t a) t) p[g](a)
$$p [g](a)
$$[g G] p[g](a)
$$[G Group](g G) p[g](a)
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestTypedFcFnRetStmt(t *testing.T) {
	code :=
		`
as(p [g](a), nat) is red
`
	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestTypedTypeVar(t *testing.T) {
	code :=
		`
as( p[as(g, G), as(g2, G)](a, as(p [g](a), nat)) , G ) is red
`

	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefPropertyVar(t *testing.T) {
	// fn ha [G Group] (g1 G, g2 property [g Group](t G)) red:
	// 1 is red

	code :=
		`
fn ha [G Group] (g1 G, g2 G) red:
	1 is red
property ha [G Group] (g1 G, g2 property [g Group](t G)) red:
	1 is red

`

	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestPropertyVar(t *testing.T) {
	// fn ha [G Group] (g1 G, g2 property [g Group](t G)) red:
	// 1 is red

	code :=
		`
$p[g, as(g2, G)](f, g)
$p[g, as(g2, G)](f, as(g3, property [g Group](t G) ))
`

	statements, err := parserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}
