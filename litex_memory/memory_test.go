package litexmemory

import (
	"errors"
	"fmt"
	parser "golitex/litex_parser"
	"math/rand"
	"testing"
	"time"
)

func TestRedBlackTree(t *testing.T) {
	// 定义比较函数
	compare := func(a, b interface{}) (int, error) {
		keyA, okA := a.(int)
		keyB, okB := b.(int)
		if !okA || !okB {
			return 0, errors.New("invalid key type")
		}
		if keyA < keyB {
			return -1, nil
		} else if keyA > keyB {
			return 1, nil
		}
		return 0, nil
	}

	tree := NewRedBlackTree(compare)

	// 插入键
	keys := []int{10, 20, 30, 15, 25}
	for _, key := range keys {
		if err := tree.Insert(key); err != nil {
			fmt.Println("Insert error:", err)
			return
		}
	}

	// 中序遍历
	fmt.Println("In-order traversal:")
	tree.InOrderTraversal(tree.Root, func(key interface{}) error {
		fmt.Println(key)
		return nil
	})
}

func TestCompareFc(t *testing.T) {
	// 初始化 FcStr
	fc1 := parser.FcStr("abc")
	fc2 := parser.FcStr("def")
	fc3 := parser.FcStr("abc")

	// 初始化 FcFnRetValue
	fc4 := parser.FcFnRetValue{
		FnName: "ghi",
		TypeParamsVarParamsPairs: []parser.TypeParamsAndParamsPair{
			{
				TypeParams: []parser.TypeVarStr{"t"}, // 初始化 TypeParams
				VarParams:  []parser.Fc{fc1},         // 初始化 VarParams
			},
		},
	}
	fc5 := parser.FcFnRetValue{
		FnName: "jkl",
		TypeParamsVarParamsPairs: []parser.TypeParamsAndParamsPair{
			{
				TypeParams: []parser.TypeVarStr{}, // 初始化 TypeParams
				VarParams:  []parser.Fc{},         // 初始化 VarParams
			},
		},
	}
	fc6 := parser.FcFnRetValue{
		FnName: "ghi",
		TypeParamsVarParamsPairs: []parser.TypeParamsAndParamsPair{
			{
				TypeParams: []parser.TypeVarStr{"t"}, // 初始化 TypeParams
				VarParams:  []parser.Fc{fc3},         // 初始化 VarParams
			},
		},
	}
	fc7 := parser.FcFnRetValue{
		FnName: "ghi",
		TypeParamsVarParamsPairs: []parser.TypeParamsAndParamsPair{
			{
				TypeParams: []parser.TypeVarStr{"t"}, // 初始化 TypeParams
				VarParams:  []parser.Fc{fc2},         // 初始化 VarParams
			},
		},
	}

	fc8 := parser.FcMemChain{
		ChainOfMembers: []parser.Fc{fc1, fc2},
	}
	fc9 := parser.FcMemChain{
		// fc3, fc2,
		ChainOfMembers: []parser.Fc{fc3, fc2},
	}
	fc10 := parser.FcMemChain{
		// &fc4, &fc6,
		ChainOfMembers: []parser.Fc{&fc4, &fc6},
	}
	fc11 := parser.FcMemChain{
		// &fc4, &fc7,
		ChainOfMembers: []parser.Fc{&fc4, &fc7},
	}

	// 测试 FcStr 的比较
	result, err := CompareFc(fc1, fc2)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc1, fc2): expected negative value, got %d", result)
	}

	result, err = CompareFc(fc1, fc3)
	if err != nil {
		t.Fatal(err)
	}
	if result != 0 {
		t.Fatalf("compareFc(fc1, fc3): expected 0, got %d", result)
	}

	// 测试 FcFnRetValue 的比较
	result, err = CompareFc(&fc4, &fc5)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc4, fc5): expected negative value, got %d", result)
	}

	result, err = CompareFc(&fc4, &fc6)
	if err != nil {
		t.Fatal(err)
	}
	if result != 0 {
		t.Fatalf("compareFc(fc4, fc6): expected 0, got %d", result)
	}

	result, err = CompareFc(&fc5, &fc6)
	if err != nil {
		t.Fatal(err)
	}
	if result <= 0 {
		t.Fatalf("compareFc(fc5, fc6): expected positive value, got %d", result)
	}

	result, err = CompareFc(&fc4, &fc7)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc4, fc7): expected neg value, got %d", result)
	}

	result, err = CompareFc(&fc8, &fc9)
	if err != nil {
		t.Fatal(err)
	}
	if result != 0 {
		t.Fatalf("compareFc(fc8, fc9): expected positive value, got %d", result)
	}

	result, err = CompareFc(&fc10, &fc11)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc10, fc11): expected positive value, got %d", result)
	}
}

func TestCompareSpecFact(t *testing.T) {
	factStrings := []string{
		"$p(a)",
		"$p(b)",
		"$p(a)",
		"$p(b)",
		"$t(a)",
		"$q(a, b)",
		"$q[a,b]().t[]()",
		"$q(a, b)",
		"$q[a,b]().t[]()",
		"$q[a,b](c).t[k](f[]().g[](), t)",
		"$q[a,b](c).t[k](f[]().g[](), t)",
		"$t[a,d,c](k,g,f[]())",
		"$t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)()",
		"$t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)()",
		"$t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)()",
		"$t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)",
		"$t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)",
		"$t[a,d,c](k,g,f[]()).t[k](f[]().g[](), t)",
		"$ff()[](f[](), a.b.c.g().f[]())()()",
		"$a.b.c.g().f[]()",
		"$ff()[](f[](), a.b.c.g().f[]())()()",
		"$ff()[](f[](), a.b.c.g().f[]())()()",
		"$ff()[](f[](), a.b.c.g().f[]())()()",
		"$ff()[](f[](), a.b.c.g().f[]())()()",
		"$a.b.c.g().f[]()",
		"$f()()()()",
		"$f[]()",
		"$f[]().t[k](f[]().g[](), t)",
		"$f[]()",
		"$f[]().t[k](f[]().g[](), t)",
		"$f[]().t().g[](g[]())()()",
		"$f[]().t().g[](g[]())()()",
	}

	facts := []parser.SpecFactStmt{}
	for _, factString := range factStrings {
		topStmtSlice, err := parser.ParseSourceCode(factString)
		if err != nil {
			t.Fatalf("ParseSpecFactStmt(%q) error: %v", factString, err)
		}
		for _, stmt := range *topStmtSlice {
			asSpecFact, ok := (stmt.Stmt).(parser.SpecFactStmt)
			if !ok {
				t.Fatalf("stmt.parseSpecFactStmt() error: %v", err)
			}
			facts = append(facts, asSpecFact)
		}
	}

	res, err := specFactCompare((facts[0]), (facts[1]))
	if err != nil {
		t.Fatal(err)
	}
	fmt.Printf("t: %v\n", res)

	res, err = specFactCompare((facts[0]), (facts[0]))
	if err != nil {
		t.Fatal(err)
	}
	fmt.Printf("t: %v\n", res)

	res, err = specFactCompare((facts[0]), (facts[2]))
	if err != nil {
		t.Fatal(err)
	}
	fmt.Printf("t: %v\n", res)

	res, err = specFactCompare((facts[4]), (facts[5]))
	if err != nil {
		t.Fatal(err)
	}
	fmt.Printf("t: %v\n", res)

	start := time.Now()
	for i := 0; i < 10000000; i++ {
		j := rand.Intn(len(facts))
		k := rand.Intn(len(facts))
		specFactCompare((facts[j]), (facts[k]))
	}
	// 1.8s
	fmt.Printf("Random Compare Time taken: %v\n", time.Since(start))

	start = time.Now()
	for i := 0; i < 10000000; i++ {
		j := rand.Intn(len(facts))
		k := rand.Intn(len(facts))
		SpecFactCompareAdapter((facts[j]), (facts[k]))
	}
	// 1.9s
	fmt.Printf("Random Compare Adaptor Time taken: %v\n", time.Since(start))

	start = time.Now()
	for i := 0; i < 10000000; i++ {
		specFactCompare((facts[12]), (facts[13]))
	}
	// 7.3s
	fmt.Printf("Compare Very long the same fact Time taken: %v\n", time.Since(start))

	start = time.Now()
	for i := 0; i < 10000000; i++ {
		SpecFactCompareAdapter((facts[12]), (facts[13]))
	}
	// 7.5s, 可见强制类型转换会带来很大的开销
	fmt.Printf("Random Compare Adaptor Time taken: %v\n", time.Since(start))
}

func SpecFactCompareAdapter(a, b interface{}) (int, error) {
	knownFact, ok1 := a.(*parser.SpecFactStmt)
	givenFact, ok2 := b.(*parser.SpecFactStmt)
	if !ok1 || !ok2 {
		return 0, fmt.Errorf("expected *parser.SpecFactStmt, got %T and %T", a, b)
	}
	return specFactCompare(*knownFact, *givenFact)
}
