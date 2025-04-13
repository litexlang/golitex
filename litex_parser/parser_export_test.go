package litex_parser_test

import (
	"fmt"
	parser "golitex/litex_parser"
	"log"
	"regexp"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"
)

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
		p(x, y)
		
`
	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefPropStmt2(t *testing.T) {
	code := `
prop P(g , g2 ):
	dom:
    	f(g.g1, g2.g2)
	then:
		f(g.g1, g2.g2)

prop P(g ,  G2):
	f(g.g1, g2.g2)

axiom prop P(g ,  G2):
	dom:
    	f(g.g1, g2.g2)
	then:
		f(g.g1, g2.g2)

axiom prop P(g , g2 ):
	f(g.g1, g2.g2)

forall x :
	when:
    	f(g.g1, g2.g2)
	then:
		f(g.g1, g2.g2)


`
	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefFnStmt(t *testing.T) {
	code := `
fn P(g , g2 ) :
	dom:
    	f(g.g1, g2.g2)
	then:
		f(g.g1, g2.g2)

f(g.g1, g2.g2)
`
	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestFactStatements(t *testing.T) {
	code := `
f(g.g1, g2.g2)

forall  x :
	when: 
		f()
	then:
		f(g.g1, g2.g2)
	
`
	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestParseDefTypeStmt(t *testing.T) {
	code :=
		`
type  T2
type   T:
	type_member:
		obj 1 
		fn P(g , g2 ) :
			dom:
				f(g.g1, g2.g2)
			then:
				f(g.g1, g2.g2)
		prop P(g , g2 ):
			dom:
				f(g.g1, g2.g2)
			then:
				f(g.g1, g2.g2)
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
				p(x, y)
	
	instance_member:
		obj 2 
		fn P(g, g2 ) :
			dom:
				f(g.g1, g2.g2)
			then:
				f(g.g1, g2.g2)
		prop P(g , g2 ):
			when:
				f(g.g1, g2.g2)
			then:
				f(g.g1, g2.g2)

	know:
		p(x, y)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestParseFactStmt(t *testing.T) {
	code :=
		`
p(x, y)

forall g , g2  :
    p(x, y)

forall g , g2:
	when:
		p(x, y)
	then:
	    p(x, y)
		
		
`
	statements, err := parser.ParseSourceCode(code)
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
    p(x, y)
`
	statements, err := parser.ParseSourceCode(code)
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
	p(x, y)

	prove:
		p(x, y)

claim :
	forall  g, g2 :
		when:
			p(x, y)
		then:
			p(x, y)
	

	prove:
		p(x, y)

claim:
	p(x, y)
	p(x, y)
		
	prove:
		p(x, y)
		

`
	statements, err := parser.ParseSourceCode(code)
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
	p(x, y)
	forall g , g2 :
		when:
			p(x, y)
		then:
			p(x, y)
	
`
	statements, err := parser.ParseSourceCode(code)
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
	when:
		p(x, y)
		forall  g , g2 :
			when:
				p(x, y)
			then:
				p(x, y)

	instance_member:
	    obj 1 
		fn f(x , y ) 

	then:
	    p(x, y)
`
	statements, err := parser.ParseSourceCode(code)
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
	p(a)
`
	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestRelaFactStmt(t *testing.T) {
	code :=
		`
p(a) + 2 < (2 + 3) * 10 + 4 < 100
10 = p(a) = p(a)
`
	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestIsStmt(t *testing.T) {
	code :=
		`
( p(a) + 2 ) is q
1 * ( p(a) + 2 ) is q

`
	statements, err := parser.ParseSourceCode(code)
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
	statements, err := parser.ParseSourceCode(code)
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

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestDefPropObj(t *testing.T) {
	code :=
		`
fn ha (g1 , g2 ) :
	1 is red
	ret is red
prop ha (g1 , g2  ) :
	1 is red

`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestPropObj(t *testing.T) {
	code :=
		`
p(f, g)
p(f, as(g3, prop ))
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestFnDecl(t *testing.T) {
	code :=
		`
fn ha  (g1 , g2 ) :
    1 is red
	ret is red

claim :
	prove:
		p(x, y)

claim:
	prove_by_contradiction:
		p(x, y)

f(a, b).g.t(a, b)


`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestProofClaim(t *testing.T) {
	code :=
		`
prove:
	1 is red
`

	statements, err := parser.ParseSourceCode(code)
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

	statements, err := parser.ParseSourceCode(code)
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
		when:
			f(g.g1, g2.g2)
		then:
			f(g.g1, g2.g2)
	prove:
		f(g.g1, g2.g2)
		f(g.g1, g2.g2)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestInlineIfStmt(t *testing.T) {
	code := `
when f(g.g1, g2.g2), forall p() {p()} { p()}

forall g :
	when:
		p()
		forall g :
			when:
				q()
			then:
				t()
	then:
		t()
	
prop P(g , g2 ):
	when:
		when f(g.g1, g2.g2), when f(g.g1, g2.g2) {p()}  {p()}
	then:
		p()
prove:
	when f(g.g1, g2.g2), forall p() {p()}  {p()}
	when f(g.g1, g2.g2) { p()}

forall g , g2:
	when:
		p(x, y)
		when f(g.g1, g2.g2) {p()}ÂÂ
	then:
	    p(x, y)

-1 is red
`

	statements, err := parser.ParseSourceCode(code)
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

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestForall(t *testing.T) {
	code := `
forall g G, g2 G2:
	when:
		G(g)
		G(g2)
		p(x, y)
		when f(g.g1, g2.g2) {p()}
	then:
		p(x, y)
forall <G Group, G2 Group> g G, g2 G2:
	G(g)
	G(g2)
	p(x, y)
	when f(g.g1, g2.g2) {p()}
	then:
		p(x, y)

forall () p() {p()}
`

	statements, err := parser.ParseSourceCode(code)
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

	statements, err := parser.ParseSourceCode(code)
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

	statements, err := parser.ParseSourceCode(code)
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
	re := regexp.MustCompile(`^([^\[\]]+)((?:\[[^\]]+\]\([^\)]+\))*)`)

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
p(x, y)
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

	statements, err := parser.ParseSourceCode(code)
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
//    p(x, y)

forall g, g2:
    p(x, y)

`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestFcWithPkgName(t *testing.T) {
	code := `
a::b is red::blue
p(x, y)(red::blue, g::f(1,2)(3,4))
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestForallStmt3(t *testing.T) {
	code := `
forall <G Group, G2 Group> g G, g2 G2:
	G(g)
	G(g2)
	p(x, y)
	then:
		p(x, y)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestForallStmt4(t *testing.T) {
	code := `
forall <G Group, G2 Group> g G, g2 G2:
	G(g); G(g2);
	G(g); G(g2);P(x, y);
	p(x, y)
	then:
		p(x, y)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestFnPropExistProp(t *testing.T) {
	code := `
fn f(x S, y G) nat:
	G(g); G(g2);
	G(g); G(g2);P(x, y);
	p(x, y)
	then:
		p(x, y)

prop f(x S, y G):
	G(g); G(g2);
	G(g); G(g2);P(x, y);
	p(x, y)
	then:
		p(x, y)

fn at(a nat, b nat) nat:
	when:
    	p(x, y)
	Q(x,y)


exist_prop f(x S, y G) a fn, b S, c G:
	G(g); G(g2);
	G(g); G(g2);P(x, y);
	p(x, y)
	then:
		p(x, y)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestRelaFactStmt2(t *testing.T) {
	code := `
p(x, y)
x < y
1 = 2
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestUniFactStmt3(t *testing.T) {
	code := `
forall x A:
	p(x)
	then:
		p(x)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}
func TestUniFactStmt4(t *testing.T) {
	code := `
know:
	t = f
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}

}

func TestProve(t *testing.T) {
	code := `
prop q(x A):
	p(x)
	iff:
		t(x)

`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestIn(t *testing.T) {
	code := `
prove:
    	know:
				x in A
    	x in A
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestFnDef(t *testing.T) {
	code := `
fn f(x A) B:
	p(x)
	then:
		q(f(x))
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestForall2(t *testing.T) {
	code := `
know forall x A:
	p(x)
  	forall y A:
					t(y)
					then:
		 				q(x)
	q(x)
know p(x)
q(1) // true, 因为 p(x) 被match 了

know forall x A:
	p(x)
  	forall y A:
					t(y)
					then:
		 				q(x)
	q(x)


know :
	forall x A:
		p(x)
		forall x B:
			t(y)
		then:
				p(x)

know forall x A:
		p(x)
		forall x B:
			t(y, x)
		then:
				p(x)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestForall3(t *testing.T) {
	code := `
know forall x A:
		p(x)
		forall y A:
								t(y)
		then:
			h(x)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestForall4(t *testing.T) {
	code := `
know forall x A:
		forall y A:
								t(y)

`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		log.Fatalf("%s", err)
	}

}

func TestForall5(t *testing.T) {
	code := `
know forall x A:
	p(x)
	forall x B:
		t(y)
	then:
			p(x)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestFn(t *testing.T) {
	code := `
fn f(x A) B:
	dom(x)
	then:
		ret(x)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestForall6(t *testing.T) {
	code := `
know forall x A:
	p(x)
	forall y B:
		forall z B:
			t(y,z)
		then:
			p(2)
		  t(x)
	then:
			p(x)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}

func TestIndent(t *testing.T) {
	code := `
forall x A:
	x larger_than A
	then:
		p(x)
`

	statements, err := parser.ParseSourceCode(code)
	if err == nil {
		fmt.Printf("%v\n", statements)
	} else {
		t.Fatal(err)
	}
}
