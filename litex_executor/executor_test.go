package litexexecutor

import (
	"fmt"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
	"math/rand"
	"strings"
	"testing"
	"time"
)

func TestStoreNewVar(t *testing.T) {
	code := `var a G`
	statements, err := parser.ParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	env := memory.NewEnv()
	executor := Executor{env, []string{}, execError, 0}
	for _, topStmt := range *statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(executor.output)
		fmt.Println(executor.message)
	}

	entry, _ := env.VarMemory.Get("a")
	println(string(entry.Tp.Value.(parser.FcVarTypeStrValue)))
}

func TestKnow(t *testing.T) {
	code := `know $p(a)`
	statements, err := parser.ParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	env := memory.NewEnv()
	executor := *newExecutor()
	executor.env = env
	for _, topStmt := range *statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(executor.output)
		fmt.Println(executor.message)
	}
}

func TestVerifier(t *testing.T) {
	code := `know $p(a)`
	statements, err := parser.ParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	env := memory.NewEnv()
	executor := *newExecutor()
	executor.env = env
	for _, topStmt := range *statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		executor.printlnOutputMessage()
	}

	testCodes := "$p(b)\n$p(a)"
	testStatements, err := parser.ParseSourceCode(testCodes)
	if err != nil {
		t.Fatal(err)
	}

	for _, testCode := range *testStatements {
		err := executor.TopLevelStmt(&testCode)
		if err != nil {
			t.Fatal(err)
		}
		executor.printlnOutputMessage()
	}
}

func TestVerifier2(t *testing.T) {
	factStrings := []string{
		"know $p(a)",
		"know $p(b)",
		"know $p(a)",
		"know $p(b)",
		"know $t(a)",
		"know $q(a, b)",
		"know $q[a,b]().t[]()",
		"know $q(a, b)",
		"know $q[a,b]().t[]()",
		"know $q[a,b](c).t[k](f[]().g[](), t)",
		"know $q[a,b](c).t[k](f[]().g[](), t)",
		"know $t[a,d,c](k,g,f[]())",
		"know $t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)()",
		"know $t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)()",
		"know $t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)()",
		"know $t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)",
		"know $t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)",
		"know $t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)",
		"know $ff()[](f[](), a.b.c.g().f[]())()()",
		"know $a.b.c.g().f[]()",
		"know $ff()[](f[](), a.b.c.g().f[]())()()",
		"know $ff()[](f[](), a.b.c.g().f[]())()()",
		"know $ff()[](f[](), a.b.c.g().f[]())()()",
		"know $ff()[](f[](), a.b.c.g().f[]())()()",
		"know $a.b.c.g().f[]()",
		"know $f()()()()",
		"know $f[]()",
		"know $f[]().t[k](f[]().g[](), t)",
		"know $f[]()",
		"know $f[]().t[k](f[]().g[](), t)",
		"know $f[]().t().g[](g[]())()()",
		"know $f[]().t().g[](g[]())()()",
	}

	code := strings.Join(factStrings, "\n")
	statements, err := parser.ParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	env := memory.NewEnv()
	executor := *newExecutor()
	executor.env = env
	for _, topStmt := range *statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
	}

	testCodes := "$ff()[](f[](), a.b.c.g().f[]())()()"
	start := time.Now()
	for i := 0; i < 100; i++ {
		testStatements, err := parser.ParseSourceCode(testCodes)
		for _, testCode := range *testStatements {
			err := executor.TopLevelStmt(&testCode)
			if err != nil {
				t.Fatal(err)
			}
		}
		if err != nil {
			t.Fatal(err)
		}
	}
	// 2.6ms
	fmt.Printf("Check Time taken: %v\n", time.Since(start))
}

func randFuncFact() *parser.FuncFactStmt {
	stmt := parser.FuncFactStmt{IsTrue: true, Fc: randomFcGenerator()}
	return &stmt
}

func randomFcGenerator() parser.Fc {

	e := rand.Intn(3)

	if e == 0 {
		// generate a random number from 1 to 10
		return randFcString()
	}

	if e == 1 {
		return randFcFnRetValue()
	}

	if e == 2 {
		return randFcChain()
	}
	return nil
}

func randFcChain() *parser.FcMemChain {
	fcArr := []parser.Fc{}
	round := rand.Intn(3) + 2
	for i := 0; i < round; i++ {
		fcArr = append(fcArr, randFcFnRetValue())
	}
	return &parser.FcMemChain{ChainOfMembers: fcArr}
}

func randFcString() parser.FcStr {
	length := rand.Intn(10) + 1
	bytes := make([]byte, length)
	for i := 0; i < length; i++ {
		bytes[i] = byte(rand.Intn(26) + 65)
	}
	return parser.FcStr(bytes)
}

func randFcFnRetValue() *parser.FcFnRetValue {
	fnName := randFcString()
	round := rand.Intn(3) + 1
	typeParamVarParamsPairs := []parser.TypeParamsAndParamsPair{}
	for i := 0; i < round; i++ {
		typeParamVarParamsPairs = append(typeParamVarParamsPairs, parser.TypeParamsAndParamsPair{TypeParams: *randTypeParams(), VarParams: *randVarParams()})
	}
	return &parser.FcFnRetValue{FnName: fnName, TypeParamsVarParamsPairs: typeParamVarParamsPairs}
}

func randTypeParams() *[]parser.TypeVarStr {
	round := rand.Intn(3) + 1
	typeVars := []parser.TypeVarStr{}
	for i := 0; i < round; i++ {
		length := rand.Intn(10) + 1
		bytes := make([]byte, length)
		for i := 0; i < length; i++ {
			bytes[i] = byte(rand.Intn(26) + 65)
		}
		typeVars = append(typeVars, parser.TypeVarStr(bytes))
	}
	return &typeVars
}

func randVarParams() *[]parser.Fc {
	round := rand.Intn(3) + 1
	varParams := []parser.Fc{}
	for i := 0; i < round; i++ {
		varParams = append(varParams, randFcString()) // 这里必须是randFcString不能是randFc，否则会因为内存溢出停掉
	}
	return &varParams
}

func randCondStmt() *parser.CondFactStmt {
	randomNumberOfCondFacts := rand.Intn(3) + 1
	randomNumberOfThenFacts := rand.Intn(3) + 1
	condFacts := []parser.FactStmt{}
	thenFacts := []parser.SpecFactStmt{}

	for i := 0; i < randomNumberOfCondFacts; i++ {
		condFacts = append(condFacts, randFuncFact())
	}

	for i := 0; i < randomNumberOfThenFacts; i++ {
		thenFacts = append(thenFacts, randFuncFact())
	}

	return &parser.CondFactStmt{CondFacts: condFacts, ThenFacts: thenFacts}
}

func TestKnowVerifyFuncFactSpeed(t *testing.T) {
	env := memory.NewEnv()
	executor := *newExecutor()
	executor.env = env
	topStatements := []*parser.TopStmt{}
	topVerifyStatements := []*parser.TopStmt{}

	// 数量级为 n*log(n)，因为走一遍是log(n), 走 rounds 次差不多就是 n * log(n)
	rounds := 1000000
	for i := 0; i < rounds; i++ {
		stmt := randFuncFact()
		knowStmt := parser.KnowStmt{Facts: []parser.FactStmt{stmt}}
		topKnow := parser.TopStmt{Stmt: &knowStmt, IsPub: true}
		topVerifyStatements = append(topVerifyStatements, &parser.TopStmt{Stmt: stmt, IsPub: true})
		topStatements = append(topStatements, &topKnow)
	}

	start := time.Now()
	for _, topStmt := range topStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil {
			t.Fatal(err)
		}
	}
	// 1000 rounds 3.8-4.5ms
	// 10000 rounds 51ms
	fmt.Printf("%d round know taken: %v\n", rounds, time.Since(start))

	start = time.Now()
	for _, topStmt := range topVerifyStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil || !executor.true() {
			t.Fatal(err)
		}

	}
	// 1000 rounds:6.5-7ms 大约是插入的两倍。因为你树建立完后，再遍历地去检查，确实会导致平均路过的节点数比原来多
	// 10000 69ms
	fmt.Printf("%d round verify taken: %v\n", rounds, time.Since(start))
}

func TestKnowVerifyCondFactSpeed(t *testing.T) {
	env := memory.NewEnv()
	executor := *newExecutor()
	executor.env = env
	topStatements := []*parser.TopStmt{}
	topVerifyStatements := []*parser.TopStmt{}

	rounds := 100
	for i := 0; i < rounds; i++ {
		stmt := randCondStmt()
		knowStmt := parser.KnowStmt{Facts: []parser.FactStmt{stmt}}
		topKnow := parser.TopStmt{Stmt: &knowStmt, IsPub: true}
		topVerifyStatements = append(topVerifyStatements, &parser.TopStmt{Stmt: stmt, IsPub: true})
		topStatements = append(topStatements, &topKnow)
	}

	start := time.Now()
	for _, topStmt := range topStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil {
			t.Fatal(err)
		}
	}
	// 100000 rounds know taken: 1.677706542s
	fmt.Printf("%d round know taken: %v\n", rounds, time.Since(start))

	start = time.Now()
	for _, topStmt := range topVerifyStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil || !executor.true() {
			t.Fatal(err)
		}

	}
	// 100000 rounds verify taken: 10.808512542s
	fmt.Printf("%d round verify taken: %v\n", rounds, time.Since(start))
}
