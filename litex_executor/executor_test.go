package litex_executor

import (
	"fmt"
	ast "golitex/litex_ast"
	env "golitex/litex_env"
	parser "golitex/litex_parser"
	"math/rand"
	"os"
	"slices"
	"strings"
	"testing"
	"time"
)

const (
	SmallRound       = 10
	MediumRound      = 20
	HundredRound     = 100
	TenThousandRound = 10000
	TenMillionRound  = 10000000
)

func setupAndParseStmtTest(code string, t *testing.T) []ast.TopStmt {
	topStatements, err := parser.SetupAndParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	return topStatements
}

func execStmtTest(topStmt []ast.TopStmt, t *testing.T) []string {
	env := env.NewEnv(nil, nil, "")
	executor := *NewExecutor(env)

	messages := []string{}
	for _, topStmt := range topStmt {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		messages = append(messages, strings.Join(executor.env.Msgs, "\n"))
	}
	slices.Reverse(messages)
	return messages
}

func printExecMsg(messageSlice []string) {
	for i := len(messageSlice) - 1; i >= 0; i-- {
		fmt.Println(messageSlice[i])
		fmt.Println()
		fmt.Println()
	}
}

func TestKnow(t *testing.T) {
	code := `know $p(a)`
	statements, err := parser.SetupAndParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	env := env.NewEnv(nil, nil, "")
	executor := *NewExecutor(env)
	for _, topStmt := range statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(executor.env.Msgs)
	}
}

func randSpecFact() *ast.SpecFactStmt {
	n := rand.Intn(10) + 1
	params := make([]ast.Fc, n)
	for i := 0; i < n; i++ {
		params[i] = randomFc()
	}

	stmt := ast.SpecFactStmt{IsTrue: true, PropName: *randFcAtom(), Params: params}
	return &stmt
}

func randomFc() ast.Fc {
	e := rand.Intn(2)
	if e == 0 {
		return randFcAtom()
	} else {
		return randFcFnRetValue()
	}
}

func randFcAtom() *ast.FcAtom {
	length := rand.Intn(10) + 1
	bytes := make([]byte, length)
	for i := 0; i < length; i++ {
		bytes[i] = byte(rand.Intn(26) + 65)
	}
	ret := ast.FcAtom{Value: string(bytes)}
	return &ret
}

func randFcFnRetValue() *ast.FcFn {
	fnName := randFcAtom()
	round := rand.Intn(3) + 1
	typeParamObjParamsPairs := []*ast.FcFnSeg{}
	for i := 0; i < round; i++ {
		typeParamObjParamsPairs = append(typeParamObjParamsPairs, &ast.FcFnSeg{Params: randObjParams()})
	}
	return &ast.FcFn{FnHead: *fnName, ParamSegs: typeParamObjParamsPairs}
}

func randObjParams() []ast.Fc {
	round := rand.Intn(3) + 1
	objParams := []ast.Fc{}
	for i := 0; i < round; i++ {
		objParams = append(objParams, randFcAtom())
	}
	return objParams
}

func randCondStmt() *ast.CondFactStmt {
	randomNumberOfCondFacts := rand.Intn(3) + 1
	randomNumberOfThenFacts := rand.Intn(3) + 1
	condFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

	for i := 0; i < randomNumberOfCondFacts; i++ {
		condFacts = append(condFacts, randSpecFact())
	}

	for i := 0; i < randomNumberOfThenFacts; i++ {
		thenFacts = append(thenFacts, randSpecFact())
	}

	return &ast.CondFactStmt{CondFacts: condFacts, ThenFacts: thenFacts}
}

func TestKnowVerifySpecFactSpeed(t *testing.T) {
	env := env.NewEnv(nil, nil, "")
	executor := *NewExecutor(env)
	topStatements := []*ast.TopStmt{}
	topVerifyStatements := []*ast.TopStmt{}

	// 数量级为 n*log(n)，因为走一遍是log(n), 走 rounds 次差不多就是 n * log(n)
	rounds := HundredRound

	start := time.Now()
	for i := 0; i < rounds; i++ {
		stmt := randSpecFact()
		knowStmt := ast.KnowStmt{Facts: []ast.FactStmt{stmt}}
		topKnow := ast.TopStmt{Stmt: &knowStmt, IsPub: true}
		topVerifyStatements = append(topVerifyStatements, &ast.TopStmt{Stmt: stmt, IsPub: true})
		topStatements = append(topStatements, &topKnow)
	}
	// takes 3.371321s to generate 1000000 statements
	fmt.Printf("takes %v to generate %v statements\n", time.Since(start), rounds)

	start = time.Now()
	for _, topStmt := range topStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil {
			t.Fatal(err)
		}
	}
	// 1000 rounds 3.8-4.5ms
	// 10000 rounds 51ms
	// 1000000 round know taken: 7.88127275s
	fmt.Printf("%d rounds know taken: %v\n", rounds, time.Since(start))

	start = time.Now()
	for _, topStmt := range topVerifyStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil {
			t.Fatal(err)
		}

	}
	// 1000 rounds:6.5-7ms 大约是插入的两倍。因为你树建立完后，再遍历地去检查，确实会导致平均路过的节点数比原来多
	// 10000 69ms
	// 1000000 round verify taken: 8.866167667s
	fmt.Printf("%d rounds verify taken: %v\n", rounds, time.Since(start))
}

func TestKnowVerifyCondFactSpeed(t *testing.T) {
	env := env.NewEnv(nil, nil, "")
	executor := *NewExecutor(env)
	executor.env = env
	topStatements := []*ast.TopStmt{}
	topVerifyStatements := []*ast.TopStmt{}

	rounds := HundredRound
	for i := 0; i < rounds; i++ {
		stmt := randCondStmt()
		knowStmt := ast.KnowStmt{Facts: []ast.FactStmt{stmt}}
		topKnow := ast.TopStmt{Stmt: &knowStmt, IsPub: true}
		topVerifyStatements = append(topVerifyStatements, &ast.TopStmt{Stmt: stmt, IsPub: true})
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
		if err != nil {
			t.Fatal(err)
		}

	}
	// 100000 rounds verify taken: 10.808512542s
	fmt.Printf("%d round verify taken: %v\n", rounds, time.Since(start))
}

func TestIfCondNotKnownThenUnknownIfKnownThenTrue(t *testing.T) {
	env := env.NewEnv(nil, nil, "")
	executor := *NewExecutor(env)
	executor.env = env
	topKnowStatements := []*ast.TopStmt{}
	topVerifyStatements := []*ast.TopStmt{}

	rounds := HundredRound
	for i := 0; i < rounds; i++ {
		stmt := randCondStmt()
		knowStmt := ast.KnowStmt{Facts: []ast.FactStmt{stmt}}
		topKnow := ast.TopStmt{Stmt: &knowStmt, IsPub: true}
		if i < rounds/2 {
			topVerifyStatements = append(topVerifyStatements, &ast.TopStmt{Stmt: stmt, IsPub: true})
			topKnowStatements = append(topKnowStatements, &topKnow)
		} else {
			topVerifyStatements = append(topVerifyStatements, &ast.TopStmt{Stmt: stmt, IsPub: true})
		}
	}

	start := time.Now()
	for _, topStmt := range topKnowStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil {
			t.Fatal(err)
		}
	}
	fmt.Printf("%d round know taken: %v\n", rounds, time.Since(start))

	start = time.Now()
	notVerifiedCount := 0
	notVerifiedIndexes := []int{}
	for i, topStmt := range topVerifyStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil {
			notVerifiedCount++
			notVerifiedIndexes = append(notVerifiedIndexes, i)
		}
	}
	fmt.Printf("%d statements not verified, %v\n", notVerifiedCount, notVerifiedIndexes)

	fmt.Printf("%d round verify taken: %v\n", rounds, time.Since(start))
}

func TestEqualFactMemory(t *testing.T) {
	env := env.NewEnv(nil, nil, "")
	executor := *NewExecutor(env)
	executor.env = env
	topKnowStatements := []*ast.TopStmt{}
	topVerifyStatements := []*ast.TopStmt{}

	rounds := HundredRound
	for i := 0; i < rounds; i++ {
		stmt := randEqualFact()
		knowStmt := ast.KnowStmt{Facts: []ast.FactStmt{stmt}}
		topKnowStmt := ast.TopStmt{Stmt: &knowStmt, IsPub: true}
		if i < rounds/2 {
			topVerifyStatements = append(topVerifyStatements, &ast.TopStmt{Stmt: stmt, IsPub: true})
			topKnowStatements = append(topKnowStatements, &topKnowStmt)
		} else {
			topVerifyStatements = append(topVerifyStatements, &ast.TopStmt{Stmt: stmt, IsPub: true})
		}
	}

	start := time.Now()
	for _, topStmt := range topKnowStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil {
			t.Fatal(err)
		}
	}
	fmt.Printf("%d round know taken: %v\n", rounds, time.Since(start))

	start = time.Now()
	notVerifiedCount := 0
	notVerifiedIndexes := []int{}
	for i, topStmt := range topVerifyStatements {
		err := executor.TopLevelStmt(topStmt)
		if err != nil {
			notVerifiedCount++
			notVerifiedIndexes = append(notVerifiedIndexes, i)
		}
	}
	fmt.Printf("%d statements not verified\n", notVerifiedCount)

	fmt.Printf("%d round verify taken: %v\n", rounds, time.Since(start))

	if rounds < MediumRound {
		fmt.Printf("%d statements not verified, %v\n", notVerifiedCount, notVerifiedIndexes)

		fmt.Println("know:")
		for i, topKnowStatement := range topKnowStatements {
			fmt.Printf("%d: %v\n", i, topKnowStatement)
		}

		fmt.Println("verify:")

		for i, topVerifyStmt := range topVerifyStatements {
			fmt.Printf("%d: %v\n", i, topVerifyStmt)
		}
	}
}

func randEqualFact() *ast.SpecFactStmt {
	left := randomFc()
	right := randomFc()

	return &ast.SpecFactStmt{IsTrue: true, Params: []ast.Fc{left, right}, PropName: ast.FcAtom{PkgName: "", Value: "="}}
}

func TestVerificationUsingEqual(t *testing.T) {
	code :=
		`
know:
	x = y
	$p(x)

$p(z)
$q(x)
$p(x)
$p(y)
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestCondVerifier(t *testing.T) {
	code :=
		`
know:
	when:
		$q(a)
		then:
			$p(x)

know:
	$q(a)
	x = y

$p(z)
$p(y)
$p(x)
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestEqualVerifier(t *testing.T) {
	code :=
		`
know:
	x < y
	x = a

a < y
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestWhenVerifier2(t *testing.T) {
	code :=
		`
know:
	when:
		x = 1
		then:
			x < y
	x = 1

x < y
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestForallVerifier(t *testing.T) {
	code :=
		`
forall x A:
	$p(x)
	x = y
	then:
		$p(x)
		$p(y)

forall x A:
	$p(x)
	x = y
	then:
		$p(b)

$p(x)
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestUseForallToCheck(t *testing.T) {
	code :=
		`
know:
	forall x A:
		$p(f(x))

know:
	t = f
			
$p(t(x))
$p(g(x))
$p(f(x))

know:
	forall x A:
		$p(x)

$p(ha)
$p(g(x, 100))
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestEqual(t *testing.T) {
	code :=
		`
know:
	$p(t(x))
$p(g(x))
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestProve(t *testing.T) {
	code :=
		`
prove:
    know forall x R:
        $p(x)
        then:
            $p(f(x))
    $p(f(x))
    know $p(x)
    $p(f(x))
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestFacts(t *testing.T) {
	code :=
		`
know $p(x)
$p(x)
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func readFile(filePath string) string {
	content, err := os.ReadFile(filePath)
	if err != nil {
		panic(err)
	}
	return string(content)
}

func TestPropDef(t *testing.T) {
	code :=
		`
prop q(x A):
	$p(x)
	iff:
		$t(x)

know:
	$q(1)
	$p(1)

$t(1)

know:
	$t(2)
	$p(2)

$q(2)
`
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestPropDef2(t *testing.T) {
	code := "prove:\n\tknow:\n\t\t$p(x);$p(y)\n\t$p(y)"
	topStmtSlice := setupAndParseStmtTest(code, t)
	messages := execStmtTest(topStmtSlice, t)
	printExecMsg(messages)
}

func TestAllFactCodeSeveralRounds(t *testing.T) {
	code := readFile("../litex_code_examples/litex_as_regex_matcher.lix")
	rounds := 1
	topStmtSlice := setupAndParseStmtTest(code, t)
	start := time.Now()
	for i := 0; i < rounds; i++ {
		execStmtTest(topStmtSlice, t)
		// printExecMsg(messages)
	}
	fmt.Printf("execution takes %v\n", time.Since(start))
}

func TestAllFactCode(t *testing.T) {
	start := time.Now()
	readFileTime := time.Since(start)
	start = time.Now()
	topStmtSlice := setupAndParseStmtTest(code, t)
	parseTime := time.Since(start)
	start = time.Now()
	messages := execStmtTest(topStmtSlice, t)
	executionTime := time.Since(start)
	printExecMsg(messages)
	fmt.Printf("read file takes %v\nparsing takes %v\nexecution takes %v\n", readFileTime, parseTime, executionTime)
}

func TestLastFactCode(t *testing.T) {
	start := time.Now()
	readFileTime := time.Since(start)
	start = time.Now()
	topStmtSlice := setupAndParseStmtTest(code, t)
	parseTime := time.Since(start)
	start = time.Now()
	messages := execStmtTest(topStmtSlice[len(topStmtSlice)-1:], t)
	executionTime := time.Since(start)
	printExecMsg(messages)
	fmt.Printf("read file takes %v\nparsing takes %v\nexecution takes %v\n", readFileTime, parseTime, executionTime)
}

var code = readFile("../litex_code_examples/classic_examples/def.lix")
