package litexexecutor

import (
	"fmt"
	env "golitex/litex_env"
	parser "golitex/litex_parser"
	"math/rand"
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

func TestStoreNewObj(t *testing.T) {
	code := `obj a G`
	statements, err := parser.ParseSourceCode(&code)
	if err != nil {
		t.Fatal(err)
	}
	curEnv := env.NewEnv(nil)
	executor := Executor{curEnv, &[]string{}, execError}
	for _, topStmt := range *statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(executor.output)
		fmt.Println(executor.message)
	}

	entry, _ := curEnv.ObjMemory.Get("a")
	println((entry))
}

func TestKnow(t *testing.T) {
	code := `know $p(a)`
	statements, err := parser.ParseSourceCode(&code)
	if err != nil {
		t.Fatal(err)
	}
	env := env.NewEnv(nil)
	executor := *newExecutor(env)
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
	statements, err := parser.ParseSourceCode(&code)
	if err != nil {
		t.Fatal(err)
	}
	env := env.NewEnv(nil)
	executor := *newExecutor(env)
	for _, topStmt := range *statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		executor.printlnOutputMessage()
	}

	testCodes := "$p(b)\n$p(a)"
	testStatements, err := parser.ParseSourceCode(&testCodes)
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

func randFuncFact() *parser.FuncFactStmt {
	// randomly generate n random Fc
	n := rand.Intn(10) + 1
	params := make([]parser.Fc, n)
	for i := 0; i < n; i++ {
		params[i] = randomFc()
	}

	stmt := parser.FuncFactStmt{IsTrue: true, Opt: *randFcAtom(), Params: params}
	return &stmt
}

func randomFc() parser.Fc {
	e := rand.Intn(2)
	if e == 0 {
		return randFcAtom()
	} else {
		return randFcFnRetValue()
	}
}

func randFcAtom() *parser.FcAtom {
	length := rand.Intn(10) + 1
	bytes := make([]byte, length)
	for i := 0; i < length; i++ {
		bytes[i] = byte(rand.Intn(26) + 65)
	}
	ret := parser.FcAtom{Value: string(bytes)}
	return &ret
}

func randFcFnRetValue() *parser.FcFnCallPipe {
	fnName := randFcAtom()
	round := rand.Intn(3) + 1
	typeParamObjParamsPairs := []parser.FcFnCallPipeSeg{}
	for i := 0; i < round; i++ {
		typeParamObjParamsPairs = append(typeParamObjParamsPairs, parser.FcFnCallPipeSeg{Params: *randObjParams()})
	}
	return &parser.FcFnCallPipe{FnName: *fnName, CallPipe: typeParamObjParamsPairs}
}

// func randTypeParams() *[]parser.TypeObjStr {
// 	round := rand.Intn(3) + 1
// 	typeObj := []parser.TypeObjStr{}
// 	for i := 0; i < round; i++ {
// 		length := rand.Intn(10) + 1
// 		bytes := make([]byte, length)
// 		for i := 0; i < length; i++ {
// 			bytes[i] = byte(rand.Intn(26) + 65)
// 		}
// 		typeObjs = append(typeObjs, parser.TypeObjStr(bytes))
// 	}
// 	return &typeObjs
// }

func randObjParams() *[]parser.Fc {
	round := rand.Intn(3) + 1
	objParams := []parser.Fc{}
	for i := 0; i < round; i++ {
		objParams = append(objParams, randFcAtom()) // 这里必须是randFcString不能是randFc，否则会因为内存溢出停掉
	}
	return &objParams
}

func randCondStmt() *parser.ConditionalFactStmt {
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

	return &parser.ConditionalFactStmt{CondFacts: condFacts, ThenFacts: thenFacts}
}

func TestKnowVerifyFuncFactSpeed(t *testing.T) {
	env := env.NewEnv(nil)
	executor := *newExecutor(env)
	topStatements := []*parser.TopStmt{}
	topVerifyStatements := []*parser.TopStmt{}

	// 数量级为 n*log(n)，因为走一遍是log(n), 走 rounds 次差不多就是 n * log(n)
	rounds := HundredRound

	start := time.Now()
	for i := 0; i < rounds; i++ {
		stmt := randFuncFact()
		knowStmt := parser.KnowStmt{Facts: []parser.FactStmt{stmt}}
		topKnow := parser.TopStmt{Stmt: &knowStmt, IsPub: true}
		topVerifyStatements = append(topVerifyStatements, &parser.TopStmt{Stmt: stmt, IsPub: true})
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
		if err != nil || !executor.true() {
			t.Fatal(err)
		}

	}
	// 1000 rounds:6.5-7ms 大约是插入的两倍。因为你树建立完后，再遍历地去检查，确实会导致平均路过的节点数比原来多
	// 10000 69ms
	// 1000000 round verify taken: 8.866167667s
	fmt.Printf("%d rounds verify taken: %v\n", rounds, time.Since(start))
}

func TestKnowVerifyCondFactSpeed(t *testing.T) {
	env := env.NewEnv(nil)
	executor := *newExecutor(env)
	executor.env = env
	topStatements := []*parser.TopStmt{}
	topVerifyStatements := []*parser.TopStmt{}

	rounds := HundredRound
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

func TestIfCondNotKnownThenUnknownIfKnownThenTrue(t *testing.T) {
	env := env.NewEnv(nil)
	executor := *newExecutor(env)
	executor.env = env
	topKnowStatements := []*parser.TopStmt{}
	topVerifyStatements := []*parser.TopStmt{}

	rounds := HundredRound
	for i := 0; i < rounds; i++ {
		stmt := randCondStmt()
		knowStmt := parser.KnowStmt{Facts: []parser.FactStmt{stmt}}
		topKnow := parser.TopStmt{Stmt: &knowStmt, IsPub: true}
		if i < rounds/2 {
			topVerifyStatements = append(topVerifyStatements, &parser.TopStmt{Stmt: stmt, IsPub: true})
			topKnowStatements = append(topKnowStatements, &topKnow)
		} else {
			topVerifyStatements = append(topVerifyStatements, &parser.TopStmt{Stmt: stmt, IsPub: true})
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
		if err != nil || !executor.true() {
			notVerifiedCount++
			notVerifiedIndexes = append(notVerifiedIndexes, i)
		}
	}
	fmt.Printf("%d statements not verified, %v\n", notVerifiedCount, notVerifiedIndexes)

	fmt.Printf("%d round verify taken: %v\n", rounds, time.Since(start))
}

func TestEqualFactMemory(t *testing.T) {
	env := env.NewEnv(nil)
	executor := *newExecutor(env)
	executor.env = env
	topKnowStatements := []*parser.TopStmt{}
	topVerifyStatements := []*parser.TopStmt{}

	rounds := HundredRound
	for i := 0; i < rounds; i++ {
		stmt := randEqualFact()
		knowStmt := parser.KnowStmt{Facts: []parser.FactStmt{stmt}}
		topKnowStmt := parser.TopStmt{Stmt: &knowStmt, IsPub: true}
		if i < rounds/2 {
			topVerifyStatements = append(topVerifyStatements, &parser.TopStmt{Stmt: stmt, IsPub: true})
			topKnowStatements = append(topKnowStatements, &topKnowStmt)
		} else {
			topVerifyStatements = append(topVerifyStatements, &parser.TopStmt{Stmt: stmt, IsPub: true})
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
		if err != nil || !executor.true() {
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

func randEqualFact() *parser.RelationFactStmt {
	left := randomFc()
	right := randomFc()

	return &parser.RelationFactStmt{IsTrue: true, Params: []parser.Fc{left, right}, Opt: parser.FcAtom{PkgName: "", Value: "="}}
}

func TestVerificationUsingEqual(t *testing.T) {
	env := env.NewEnv(nil)
	executor := *newExecutor(env)

	code :=
		`
know:
//	x = y
	$p(x)

$p(x)
`
	topStatements, err := parser.ParseSourceCode(&code)

	start := time.Now()
	for _, topStmt := range *topStatements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
	}
	fmt.Printf("%d rounds top stmt exec taken: %v\n", len(*topStatements), time.Since(start))

	if err == nil {
		fmt.Printf("%v\n", topStatements)
	} else {
		t.Fatal(err)
	}
}
