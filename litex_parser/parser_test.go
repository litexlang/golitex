package litexparser

import (
	"fmt"
	"regexp"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"
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
	subBody := []strBlock{
		{
			header: "concept [v G](v G):",
			body:   nil,
		},
	}
	body := []strBlock{
		{
			header: "concept [G Set](v G):",
			body:   subBody,
		},
	}
	input := strBlock{
		header: "concept [G Group[G Set](v G)]:",
		body:   body,
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

		fc, err := parser.ParseFc()

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
		TokenBlock{
			Parser{0, *tokenized1},
			[]TokenBlock{
				{
					Parser{0, *tokenized2},
					[]TokenBlock{},
				},
				{
					Parser{0, *tokenized2},
					[]TokenBlock{},
				},
			},
		}

	cur, err := block.parseForallStmt()

	if err != nil {
		t.Fatal(err)
	}
	fmt.Printf("%v", cur)

	tokenizedCond, err := tokenizeString("cond:")
	if err != nil {
		t.Fatal(err)
	}

	tokenizedThen, err := tokenizeString("then:")
	if err != nil {
		t.Fatal(err)
	}

	block2 :=
		TokenBlock{
			Parser{0, *tokenized1},
			[]TokenBlock{
				{
					Parser{0, *tokenizedCond},
					[]TokenBlock{
						{
							Parser{0, *tokenized2},
							[]TokenBlock{},
						},
					},
				},
				{
					Parser{0, *tokenizedThen},
					[]TokenBlock{
						{
							Parser{0, *tokenized2},
							[]TokenBlock{},
						},
						{
							Parser{0, *tokenized1},
							[]TokenBlock{
								{
									Parser{0, *tokenized2},
									[]TokenBlock{},
								},
								{
									Parser{0, *tokenized2},
									[]TokenBlock{},
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

func TestDefPropStmt(t *testing.T) {
	tokenized1, err := tokenizeString("prop ha [G Group] (g1 G, g2 G):")
	if err != nil {
		t.Fatal(err)
	}
	tokenized2, err := tokenizeString("$f[G, B](a, b)[C, D](c, d)")
	if err != nil {
		t.Fatal(err)
	}

	block :=
		TokenBlock{
			Parser{0, *tokenized1},
			[]TokenBlock{
				{
					Parser{0, *tokenized2},
					[]TokenBlock{},
				},
				{
					Parser{0, *tokenized2},
					[]TokenBlock{},
				},
			},
		}

	cur, err := block.parseDefPropStmt()
	if err != nil {
		t.Fatal(err)
	}
	fmt.Printf("%v", cur)

	tokenizedCond, err := tokenizeString("cond:")
	if err != nil {
		t.Fatal(err)
	}

	tokenizedThen, err := tokenizeString("then:")
	if err != nil {
		t.Fatal(err)
	}

	block2 :=
		TokenBlock{
			Parser{0, *tokenized1},
			[]TokenBlock{
				{
					Parser{0, *tokenizedCond},
					[]TokenBlock{
						{
							Parser{0, *tokenized2},
							[]TokenBlock{},
						},
					},
				},
				{
					Parser{0, *tokenizedThen},
					[]TokenBlock{
						{
							Parser{0, *tokenized2},
							[]TokenBlock{},
						},
					},
				},
			}}

	cur, err = block2.parseDefPropStmt()
	if err != nil {
		t.Fatal(err)
	}

	fmt.Printf("%v", cur)
}

func ParserTester(code string) (*[]Stmt, error) {
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := getTopLevelStmtSlice(code)
	if err != nil {
		return nil, err
	}

	blocks := []TokenBlock{}
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
	code := `concept var G Group:
	inherit:
		set
		group
	
	type_member:
		var 1 G
		fn f[G Group, G2 Group](x G, y G) G
		prop f[G Group, G2 Group](x G, y G)

	member:
		var 1 G
		fn f[G Group, G2 Group](x G, y G) G
		prop f[G Group, G2 Group](x G, y G)

	then:
		$p[G, G2](x, y)
		
`
	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefPropStmt2(t *testing.T) {
	code := `
prop P[G Group, G2 Group](g G, g2 G2):
	cond:
    	$f[G, B](g.g1, g2.g2)
	then:
		$f[G, B](g.g1, g2.g2)

prop P[G Group, G2 Group](g G, g2 G2):
	$f[G, B](g.g1, g2.g2)

axiom prop P[G Group, G2 Group](g G, g2 G2):
	cond:
    	$f[G, B](g.g1, g2.g2)
	then:
		$f[G, B](g.g1, g2.g2)

axiom prop P[G Group, G2 Group](g G, g2 G2):
	$f[G, B](g.g1, g2.g2)

forall x G:
	cond:
    	$f[G, B](g.g1, g2.g2)
	then:
		$f[G, B](g.g1, g2.g2)


`
	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefFnStmt(t *testing.T) {
	code := `
fn P[G Group, G2 Group](g G, g2 G2) fn [G Group, G2 Group](g G, g2 G2):
	cond:
    	$f[G, B](g.g1, g2.g2)
	then:
		$f[G, B](g.g1, g2.g2)

$f[G, B](g.g1, g2.g2)
`
	statements, err := ParserTester(code)
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
	cond: 
		$f[]()
	then:
		$f[G, B](g.g1, g2.g2)
	
`
	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestParseDefTypeStmt(t *testing.T) {
	code :=
		`
type var G Group

type var G Group:
	member:
		var 1 G
		fn f[G Group, G2 Group](x G, y G) G
		prop f[G Group, G2 Group](x G, y G)

	then:
		$p[G, G2](x, y)

type var G Group:
	$p[G, G2](x, y)
`

	statements, err := ParserTester(code)
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
	cond:
		$p[G, G2](x, y)
	then:
	    $p[G, G2](x, y)
		forall [G Group, G2 Group] g g, g2 g2:
			cond:
				$p[G, G2](x, y)
			then:
				$p[G, G2](x, y)
		
`
	statements, err := ParserTester(code)
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
	statements, err := ParserTester(code)
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

	prove:
		$p[G, G2](x, y)

claim :
	forall [G Group, G2 Group] g g, g2 g2:
		cond:
			$p[G, G2](x, y)
		then:
			$p[G, G2](x, y)
			forall [G Group, G2 Group] g g, g2 g2:
				cond:
					$p[G, G2](x, y)
				then:
					$p[G, G2](x, y)

	prove:
		$p[G, G2](x, y)

claim:
	$p[G, G2](x, y)
	$p[G, G2](x, y)
		
	prove:
		$p[G, G2](x, y)
		

`
	statements, err := ParserTester(code)
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
		cond:
			$p[G, G2](x, y)
		then:
			$p[G, G2](x, y)
			forall [G Group, G2 Group] g g, g2 g2:
				cond:
					$p[G, G2](x, y)
				then:
					$p[G, G2](x, y)
`
	statements, err := ParserTester(code)
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
	cond:
		$p[G, G2](x, y)
		forall [G Group, G2 Group] g g, g2 g2:
			cond:
				$p[G, G2](x, y)
			then:
				$p[G, G2](x, y)

	member:
	    var 1 G
		fn f[G Group, G2 Group](x G, y G) G

	then:
	    $p[G, G2](x, y)
`
	statements, err := ParserTester(code)
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
	statements, err := ParserTester(code)
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
	statements, err := ParserTester(code)
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
member [G Group](g G) 		prop f[G Group, G2 Group](x G, y G)
`
	statements, err := ParserTester(code)
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
	statements, err := ParserTester(code)
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
	statements, err := ParseSourceCode(code)
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
	statements, err := ParseSourceCode(code)
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
	statements, err := ParserTester(code)
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
	statements, err := ParserTester(code)
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

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefPropVar(t *testing.T) {
	// fn ha [G Group] (g1 G, g2 prop [g Group](t G)) red:
	// 1 is red

	code :=
		`
fn ha [G Group] (g1 G, g2 G) red:
	1 is red
prop ha [G Group] (g1 G, g2 prop [g Group](t G)) red:
	1 is red

`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestPropVar(t *testing.T) {
	// fn ha [G Group] (g1 G, g2 prop [g Group](t G)) red:
	// 1 is red

	code :=
		`
$p[g, as(g2, G)](f, g)
$p[g, as(g2, G)](f, as(g3, prop [g Group](t G) ))
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestFnDecl(t *testing.T) {
	// fn ha [G Group] (g1 G, g2 prop [g Group](t G)) red:
	// 1 is red

	code :=
		`
fn ha [G Group] (g1 G, g2 ?prop, g3 ? var, g4 ? fn) red:
    1 is red

		
fn ha [G Group] (g1 G, g2 prop [g G, g2 G] (t G) ) red:
    1 is red

claim :
	prove:
		$p[G, G2](x, y)

claim:
	prove_by_contradiction:
		$p[G, G2](x, y)

$f[G, B](a, b).g[G, B].t(a, b)


`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestProofClaim(t *testing.T) {
	// fn ha [G Group] (g1 G, g2 prop [g Group](t G)) red:
	// 1 is red

	code :=
		`
prove:
	1 is red
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestSequenceOfFcCallingOneAnother(t *testing.T) {
	code :=
		`
h[]().g[c](d).t is red
f[G, B](a, b).g[G, B].t(a, b) is red
f(t) is red

`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefTypeStmt(t *testing.T) {
	code := `
type G
type G impl Group
know $Group(G)
know forall G Group:
	$Group(G)
type var A G:	// type name is G, A is name for "self"
	then:
		know $Group(G)
type fn f[G Group, G2 Group](x G, y G) G:
	then:
		know $Group(G)
type prop f[G Group, G2 Group](x G, y G):
	then:
		know $Group(G)
type var A G:
	member:
		prop f[]()
		prop f[G Group, G2 Group](x G, y G)
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestNamedClaimStmt(t *testing.T) {
	code := `
thm: 
	prop P[G Group, G2 Group](g G, g2 G2):
		cond:
			$f[G, B](g.g1, g2.g2)
		then:
			$f[G, B](g.g1, g2.g2)
	prove:
		$f[G, B](g.g1, g2.g2)
		$f[G, B](g.g1, g2.g2)
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestInlineIfStmt(t *testing.T) {
	code := `
when $f[G, B](g.g1, g2.g2), forall [a A] $p() {$p()} { $p()}

forall g G:
	cond:
		$p()
		forall g B:
			cond:
				$q()
			then:
				$t()
	then:
		$t()
	
prop P[G Group, G2 Group](g G, g2 G2):
	cond:
		when $f[G, B](g.g1, g2.g2), when $f[G, B](g.g1, g2.g2) {$p()}  {$p()}
	then:
		$p()
prove:
	when $f[G, B](g.g1, g2.g2), forall [a A] $p() {$p()}  {$p()}
	when $f[G, B](g.g1, g2.g2) { $p()}

forall [G Group, G2 Group] g g, g2 g2:
	cond:
		$p[G, G2](x, y)
		when $f[G, B](g.g1, g2.g2) {$p()}
	then:
	    $p[G, G2](x, y)

-1 is red
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestPrecedence(t *testing.T) {
	code := `
-1 * 2 is red
-1 is red
1 + 2 * 3 is red
1 + (1 -3) * 8 -7 is red
a.b.c.d.e.f is red
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestForall(t *testing.T) {
	code := `
forall [G Group, G2 Group] g g, g2 g2:
	cond:
		$p[G, G2](x, y)
		when $f[G, B](g.g1, g2.g2) {$p()}
	then:
		$p[G, G2](x, y)
when $f[G, B](g.g1, g2.g2), forall [a A] $p() {$p()}  {$p()}
forall [a A] $p() {$p()}
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestTypeInit(t *testing.T) {
	code := `
// Group is a concept, 
type impl Group var A G:
	then:
		$S(A)
		know $Group(G)

type impl EuclidSpace var A S:	// type name is G, A is name for "self"
	then:
		$S(A)
		know $Group(G)

when:
	Socratic is human
	then:
		Socratic is mortal	
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestFc2(t *testing.T) {
	code := `
f(1,2)(3,v).F(a.b.c(4,5),6) is red	
f(1,2)(3,v).F(a.b.c(4,5),6) is red
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestHowManyCPUCores(t *testing.T) {
	fmt.Println("CPU:", runtime.NumCPU())

	timeStart := time.Now()
	var wg sync.WaitGroup
	for i := 0; i < 1000000; i++ { // 尝试创建 100 万个 goroutine
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			time.Sleep(5 * time.Second) // 模拟任务
			fmt.Printf("Goroutine %d done\n", id)
		}(i)
	}
	wg.Wait()
	fmt.Println("All goroutines done")
	timeEnd := time.Now()

	fmt.Printf("Time used: %v\n", timeEnd.Sub(timeStart))
}

func TestHowManyCPUCores2(t *testing.T) {
	var wg sync.WaitGroup
	runtime.GOMAXPROCS(2)
	// time start
	timeStart := time.Now()
	// time end

	for i := 0; i < 1000000; i++ { // 尝试创建 100 万个 goroutine
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			time.Sleep(5 * time.Second) // 模拟任务
			fmt.Printf("Goroutine %d done\n", id)
		}(i)
	}
	wg.Wait()
	fmt.Println("All goroutines done")
	timeEnd := time.Now()

	fmt.Printf("Time used: %v\n", timeEnd.Sub(timeStart))
}

func TestNewFnRetValue(t *testing.T) {
	input := "opt1[para1](value1)[para2](value2).opt2[para3](value3)[para4](value4).opt3[para5](value5)[para6](value6)"

	// 按 . 分割字符串
	blocks := strings.Split(input, ".")

	// 定义正则表达式来提取 opt 和 [paras](paras) 对
	re := regexp.MustCompile(`^([^\[\]]+)((?:\[[^\]]+\]\([^\)]+\))*)$`)

	for _, block := range blocks {
		matches := re.FindStringSubmatch(block)
		if len(matches) < 3 {
			fmt.Println("Invalid block:", block)
			continue
		}

		name := matches[1]
		pairs := matches[2]

		// 提取 [paras](paras) 对
		pairRe := regexp.MustCompile(`\[([^\]]+)\]\(([^\)]+)\)`)
		pairMatches := pairRe.FindAllStringSubmatch(pairs, -1)

		fmt.Printf("Name: %s\n", name)
		for _, pair := range pairMatches {
			key := pair[1]
			value := pair[2]
			fmt.Printf("  Pair: [%s](%s)\n", key, value)
		}
	}
}

func TestNewParseFcAtom(t *testing.T) {
	code := `
a is red
a.b is red
a.f() is red
a()() is red
a.b.c.d.e.f() is red
a.b.c.d.e.f[x,y]() is red
a.b.c.d()().e.f[x,y](z)() is red
1.b is red
1.2.b()().c.d.e.f() is red
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}
