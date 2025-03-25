package litexcomparator

import (
	"fmt"
	parser "golitex/litex_parser"
	"math/rand"
	"testing"
)

func TestCompareFc(t *testing.T) {
	// 初始化 FcStr
	fc1 := parser.FcAtom{Value: "abc"}
	fc2 := parser.FcAtom{Value: "def"}
	fc3 := parser.FcAtom{Value: "abc"}

	// 初始化 FcFnRetValue
	fc4 := parser.FcFnCallPipe{
		FnName: parser.FcAtom{Value: "ghi"},
		CallPipe: []parser.FcFnCallPipeSeg{
			{
				// TypeParams: []parser.TypeObjStr{"t"}, // 初始化 TypeParams
				Params: []parser.Fc{&fc1}, // 初始化 ObjParams
			},
		},
	}
	fc5 := parser.FcFnCallPipe{
		FnName: parser.FcAtom{Value: "jkl"},
		CallPipe: []parser.FcFnCallPipeSeg{
			{
				// TypeParams: []parser.TypeObjStr{}, // 初始化 TypeParams
				Params: []parser.Fc{}, // 初始化 ObjParams
			},
		},
	}
	fc6 := parser.FcFnCallPipe{
		FnName: parser.FcAtom{Value: "ghi"},
		CallPipe: []parser.FcFnCallPipeSeg{
			{
				// TypeParams: []parser.TypeObjStr{"t"}, // 初始化 TypeParams
				Params: []parser.Fc{&fc3}, // 初始化 ObjParams
			},
		},
	}
	fc7 := parser.FcFnCallPipe{
		FnName: parser.FcAtom{Value: "ghi"},
		CallPipe: []parser.FcFnCallPipeSeg{
			{
				// TypeParams: []parser.TypeObjStr{"t"}, // 初始化 TypeParams
				Params: []parser.Fc{&fc2}, // 初始化 ObjParams
			},
		},
	}

	// fc8 := parser.FcChain{
	// 	ChainOfMembers: []parser.FcChainMem{fc1, fc2},
	// }
	// fc9 := parser.FcChain{
	// 	// fc3, fc2,
	// 	ChainOfMembers: []parser.FcChainMem{fc3, fc2},
	// }
	// fc10 := parser.FcChain{
	// 	// &fc4, &fc6,
	// 	ChainOfMembers: []parser.FcChainMem{&fc4, &fc6},
	// }
	// fc11 := parser.FcChain{
	// 	// &fc4, &fc7,
	// 	ChainOfMembers: []parser.FcChainMem{&fc4, &fc7},
	// }

	// 测试 FcStr 的比较
	result, err := CmpFc(&fc1, &fc2)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc1, fc2): expected negative value, got %d", result)
	}

	result, err = CmpFc(&fc1, &fc3)
	if err != nil {
		t.Fatal(err)
	}
	if result != 0 {
		t.Fatalf("compareFc(fc1, fc3): expected 0, got %d", result)
	}

	// 测试 FcFnRetValue 的比较
	result, err = CmpFc(&fc4, &fc5)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc4, fc5): expected negative value, got %d", result)
	}

	result, err = CmpFc(&fc4, &fc6)
	if err != nil {
		t.Fatal(err)
	}
	if result != 0 {
		t.Fatalf("compareFc(fc4, fc6): expected 0, got %d", result)
	}

	result, err = CmpFc(&fc5, &fc6)
	if err != nil {
		t.Fatal(err)
	}
	if result <= 0 {
		t.Fatalf("compareFc(fc5, fc6): expected positive value, got %d", result)
	}

	result, err = CmpFc(&fc4, &fc7)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc4, fc7): expected neg value, got %d", result)
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
	}

	facts := []parser.SpecFactStmt{}
	for _, factString := range factStrings {
		topStmtSlice, err := parser.ParseSourceCode(&factString)
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

	rounds := 10
	for i := range rounds {
		n := rand.Intn(len(factStrings))
		m := rand.Intn(len(factStrings))
		out, err := CmpSpecFact(facts[n], facts[m])
		if err != nil {
			t.Fatalf("error: %v", err)
		}
		println("%v(%v): %v, %v", i, out, facts[n].String(), facts[m].String())
	}
}

func SpecFactCompareAdapter(a, b interface{}) (int, error) {
	knownFact, ok1 := a.(*parser.SpecFactStmt)
	givenFact, ok2 := b.(*parser.SpecFactStmt)
	if !ok1 || !ok2 {
		return 0, fmt.Errorf("expected *parser.SpecFactStmt, got %T and %T", a, b)
	}
	return CmpSpecFact(*knownFact, *givenFact)
}
