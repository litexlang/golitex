package litexcomparator_test

import (
	cmp "golitex/litex_comparator"
	parser "golitex/litex_parser"
	"testing"
)

func TestCompareFc(t *testing.T) {
	// 初始化 FcStr
	fc1 := parser.FcAtom{OptName: "abc"}
	fc2 := parser.FcAtom{OptName: "def"}
	fc3 := parser.FcAtom{OptName: "abc"}

	// 初始化 FcFnRetValue
	fc4 := parser.FcFnCallPipe{
		FnHead: parser.FcAtom{OptName: "ghi"},
		CallPipe: []parser.FcFnCallPipeSeg{
			{
				// TypeParams: []parser.TypeObjStr{"t"}, // 初始化 TypeParams
				Params: []parser.Fc{&fc1}, // 初始化 ObjParams
			},
		},
	}
	fc5 := parser.FcFnCallPipe{
		FnHead: parser.FcAtom{OptName: "jkl"},
		CallPipe: []parser.FcFnCallPipeSeg{
			{
				// TypeParams: []parser.TypeObjStr{}, // 初始化 TypeParams
				Params: []parser.Fc{}, // 初始化 ObjParams
			},
		},
	}
	fc6 := parser.FcFnCallPipe{
		FnHead: parser.FcAtom{OptName: "ghi"},
		CallPipe: []parser.FcFnCallPipeSeg{
			{
				// TypeParams: []parser.TypeObjStr{"t"}, // 初始化 TypeParams
				Params: []parser.Fc{&fc3}, // 初始化 ObjParams
			},
		},
	}
	fc7 := parser.FcFnCallPipe{
		FnHead: parser.FcAtom{OptName: "ghi"},
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
	result, err := cmp.CmpFcLiterally(&fc1, &fc2)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc1, fc2): expected negative value, got %d", result)
	}

	result, err = cmp.CmpFcLiterally(&fc1, &fc3)
	if err != nil {
		t.Fatal(err)
	}
	if result != 0 {
		t.Fatalf("compareFc(fc1, fc3): expected 0, got %d", result)
	}

	// 测试 FcFnRetValue 的比较
	result, err = cmp.CmpFcLiterally(&fc4, &fc5)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc4, fc5): expected negative value, got %d", result)
	}

	result, err = cmp.CmpFcLiterally(&fc4, &fc6)
	if err != nil {
		t.Fatal(err)
	}
	if result != 0 {
		t.Fatalf("compareFc(fc4, fc6): expected 0, got %d", result)
	}

	result, err = cmp.CmpFcLiterally(&fc5, &fc6)
	if err != nil {
		t.Fatal(err)
	}
	if result <= 0 {
		t.Fatalf("compareFc(fc5, fc6): expected positive value, got %d", result)
	}

	result, err = cmp.CmpFcLiterally(&fc4, &fc7)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc4, fc7): expected neg value, got %d", result)
	}

}
