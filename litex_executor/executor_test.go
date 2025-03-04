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
	executor := Executor{env, []string{}, ExecTrue}
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
	executor := Executor{env, []string{}, ExecTrue}
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
	executor := Executor{env, []string{}, ExecTrue}
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
	executor := Executor{env, []string{}, ExecTrue}
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

func TestKnowSpeed(t *testing.T) {
	env := memory.NewEnv()
	executor := Executor{env, []string{}, ExecTrue}
	statements := []*parser.TopStmt{}

	rounds := 1000
	for i := 0; i < rounds; i++ {
		top := parser.TopStmt{randomKnowStmt(), true}
		statements = append(statements, &top)
	}

	start := time.Now()
	for _, topStmt := range statements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil {
			t.Fatal(err)
		}
	}
	fmt.Printf("%d rounds taken: %v\n", rounds, time.Since(start))

}

func randomKnowStmt() *parser.KnowStmt {
	stmt := parser.FuncFactStmt{true, randomFcGenerator()}
	knowStmt := parser.KnowStmt{[]parser.FactStmt{&stmt}}
	return &knowStmt
}

func randomFcGenerator() parser.Fc {
	const (
		strEnum   = 0
		fnRetEnum = 1
		chainEnum = 2
	)
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
		fcArr = append(fcArr, randomFcGenerator())
	}
	a := parser.FcMemChain(fcArr)
	return &a
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
		typeParamVarParamsPairs = append(typeParamVarParamsPairs, parser.TypeParamsAndParamsPair{*randTypeParams(), *randVarParams()})
	}
	return &parser.FcFnRetValue{fnName, typeParamVarParamsPairs}
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
		varParams = append(varParams, randomFcGenerator())
	}
	return &varParams
}
