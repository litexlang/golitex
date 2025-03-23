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

// Test given string
func TestLexerFromString(t *testing.T) {
	content := `
def add(a, b):
    return a + b
`
	blocks, err := GetTopLevelStmtSlice(&content)
	if err != nil {
		t.Fatalf(err.Error())
	}

	for _, block := range blocks.Body {
		fmt.Println(block.String())
	}

	// Test invalid syntax
	_, err = GetTopLevelStmtSlice(&content)
	if err != nil {
		t.Fatalf("Expected error for invalid syntax")
	}
}

func TestSplitString(t *testing.T) {
	input := []string{"interface (v ):"}
	for _, s := range input {
		tok := newTokenizer(&s)
		tokens, err := tok.tokenizeString()

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
			Header: "interface (v ):",
			Body:   nil,
		},
	}
	body := []strBlock{
		{
			Header: "interface (v ):",
			Body:   subBody,
		},
	}
	input := strBlock{
		Header: "interface (v ):",
		Body:   body,
	}

	parsedBlock, err := TokenizeStmtBlock(&input)
	if err != nil {
		t.Fatalf(err.Error())
	}

	fmt.Println(parsedBlock)
}

func TestParseFc(t *testing.T) {
	strings := []string{
		"f(a, b)(c, d)",
		"f(a, b).g.t(a, b)",
	}

	for _, s := range strings {
		tok := newTokenizer(&s)
		tokens, err := tok.tokenizeString()
		if err != nil {
			t.Fatal(err)
		}
		parser := Parser{0, *tokens}
		fc, err := parser.parseFcAtomAndFcFnRet()
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(fc)
	}
}

func TestParseBuiltinFnRetValue(t *testing.T) {
	strings := []string{
		"-1 + 2 ^ 3 * 4 / 5 + 6 + f(a, b).g.t(a, b) * f(a, b)(c, d)",
		"f(a, b).g.t(a, b) + 1.2",
		"1.2 + 1.3 * 14.2",
		"f(a, b)(c, d) + 6 * 5",
		"-1 + 2 ^ 3 * 4 / 5 + 6",
	}

	for _, s := range strings {
		tok := newTokenizer(&s)
		tokens, err := tok.tokenizeString()
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

func ParserTester(code string) (*[]Stmt, error) {
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := GetTopLevelStmtSlice(&code)
	if err != nil {
		return nil, err
	}

	blocks := []TokenBlock{}
	for _, strBlock := range slice.Body {
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
	code := `interface G :
	inherit:
		set
		group
	
	type_member:
		obj 1 
		fn f(x , y ) 
		prop f(x , y )

	instance_member:
		obj 1 
		fn f(x , y ) 
		prop f(x , y )

	then:
		$p(x, y)
		
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
prop P(g , g2 ):
	cond:
    	$f(g.g1, g2.g2)
	then:
		$f(g.g1, g2.g2)

prop P(g ,  G2):
	$f(g.g1, g2.g2)

axiom prop P(g ,  G2):
	cond:
    	$f(g.g1, g2.g2)
	then:
		$f(g.g1, g2.g2)

axiom prop P(g , g2 ):
	$f(g.g1, g2.g2)

forall x :
	cond:
    	$f(g.g1, g2.g2)
	then:
		$f(g.g1, g2.g2)


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
fn P(g , g2 ) :
	cond:
    	$f(g.g1, g2.g2)
	then:
		$f(g.g1, g2.g2)

$f(g.g1, g2.g2)
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
$f(g.g1, g2.g2)

forall  x :
	cond: 
		$f()
	then:
		$f(g.g1, g2.g2)
	
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
// type  T2
type   T:
	type_member:
		obj 1 
		fn P(g , g2 ) :
			cond:
				$f(g.g1, g2.g2)
			then:
				$f(g.g1, g2.g2)
		prop P(g , g2 ):
			cond:
				$f(g.g1, g2.g2)
			then:
				$f(g.g1, g2.g2)
		type  T:
			type_member:
				obj 3 
				fn f(x , y ) 
				prop f(x , y )
		
			instance_member:
				obj 1 
				fn f(x, y ) 
				prop f(x , y )

			know:
				$p(x, y)
	
	instance_member:
		obj 2 
		fn P(g, g2 ) :
			cond:
				$f(g.g1, g2.g2)
			then:
				$f(g.g1, g2.g2)
		prop P(g , g2 ):
			cond:
				$f(g.g1, g2.g2)
			then:
				$f(g.g1, g2.g2)

	know:
		$p(x, y)
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
$p(x, y)

forall g , g2  :
    $p(x, y)

forall g , g2:
	cond:
		$p(x, y)
	then:
	    $p(x, y)
		
		
`
	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestParseObjStmt(t *testing.T) {
	code :=
		`
obj g 
obj g :
    $p(x, y)
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
	$p(x, y)

	prove:
		$p(x, y)

claim :
	forall  g, g2 :
		cond:
			$p(x, y)
		then:
			$p(x, y)
	

	prove:
		$p(x, y)

claim:
	$p(x, y)
	$p(x, y)
		
	prove:
		$p(x, y)
		

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
	$p(x, y)
	forall g , g2 :
		cond:
			$p(x, y)
		then:
			$p(x, y)
	
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
exist_prop P(g1 , g2 ):
	cond:
		$p(x, y)
		forall  g , g2 :
			cond:
				$p(x, y)
			then:
				$p(x, y)

	instance_member:
	    obj 1 
		fn f(x , y ) 

	then:
	    $p(x, y)
`
	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestObjDeclStmt(t *testing.T) {
	code :=
		`
obj g1

obj a :
	$p(a)
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
p(a) + 2 < (2 + 3) * 10 + 4 < 100
10 = p(a) = p(a)
`
	statements, err := ParseSourceCode(&code)
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
( p(a) + 2 ) is q
1 * ( p(a) + 2 ) is q

`
	statements, err := ParseSourceCode(&code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestTypedFcFnRetStmt(t *testing.T) {
	code :=
		`
as(p (a), nat) is red
`
	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestTypedTypeObj(t *testing.T) {
	code :=
		`
as( p(a, as(p (a), nat)) , G ) is red
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefPropObj(t *testing.T) {
	// fn ha [G Group] (g1 G, g2 prop [g Group](t G)) red:
	// 1 is red

	code :=
		`
fn ha (g1 , g2 ) :
	1 is red
	ret is red
prop ha (g1 , g2  ) :
	1 is red

`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestPropObj(t *testing.T) {
	// fn ha [G Group] (g1 G, g2 prop [g Group](t G)) red:
	// 1 is red

	code :=
		`
$p(f, g)
$p(f, as(g3, prop ))
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
// fn ha  (g1 , g2 , g3 , g4 ) red:  // 不行，因为现在不把返回值直接写在后面
//    1 is red

		
fn ha  (g1 , g2 ) :
    1 is red
	ret is red

claim :
	prove:
		$p(x, y)

claim:
	prove_by_contradiction:
		$p(x, y)

$f(a, b).g.t(a, b)


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
h().g(d).t is red
f(a, b).g.t(a, b) is red
f(t) is red

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
	prop P(g , g2):
		cond:
			$f(g.g1, g2.g2)
		then:
			$f(g.g1, g2.g2)
	prove:
		$f(g.g1, g2.g2)
		$f(g.g1, g2.g2)
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
when $f(g.g1, g2.g2), forall $p() {$p()} { $p()}

forall g :
	cond:
		$p()
		forall g :
			cond:
				$q()
			then:
				$t()
	then:
		$t()
	
prop P(g , g2 ):
	cond:
		when $f(g.g1, g2.g2), when $f(g.g1, g2.g2) {$p()}  {$p()}
	then:
		$p()
prove:
	when $f(g.g1, g2.g2), forall $p() {$p()}  {$p()}
	when $f(g.g1, g2.g2) { $p()}

forall g , g2:
	cond:
		$p(x, y)
		when $f(g.g1, g2.g2) {$p()}
	then:
	    $p(x, y)

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
forall g , g2:
	cond:
		$G(g)
		$G(g2)
		$p(x, y)
		when $f(g.g1, g2.g2) {$p()}
	then:
		$p(x, y)
when $f(g.g1, g2.g2), forall $p() {$p()}  {$p()}
forall $p() {$p()}
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
	wg := sync.WaitGroup{}
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
	wg := sync.WaitGroup{}
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
	input := "opt1(value1)(value2).opt2(value3)(value4).opt3(value5)(value6)"

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
$p(x, y)
a is red
a.b is red
a.f() is red
a()() is red
a.b.c.d.e.f() is red
a.b.c.d.e.f() is red
a.b.c.d()().e.f(z)() is red
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

func TestForallStmt2(t *testing.T) {
	code := `
// since for the time being, type system is eliminated
// forall g G, g2 G2 :
//    $p(x, y)

forall g, g2:
    $p(x, y)

`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestFcWithPkgName(t *testing.T) {
	code := `
a::b is red::blue
$p(x, y)(red::blue, g::f(1,2)(3,4))
`

	statements, err := ParserTester(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}
