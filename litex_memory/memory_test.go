package litexmemory

import (
	"errors"
	"fmt"
	parser "golitex/litex_parser"
	"testing"
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

	// 创建红黑树
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
	tree.InOrderTraversal(tree.root, func(key interface{}) error {
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

	// 测试 FcStr 的比较
	result, err := compareFc(fc1, fc2)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc1, fc2): expected negative value, got %d", result)
	}

	result, err = compareFc(fc1, fc3)
	if err != nil {
		t.Fatal(err)
	}
	if result != 0 {
		t.Fatalf("compareFc(fc1, fc3): expected 0, got %d", result)
	}

	// 测试 FcFnRetValue 的比较
	result, err = compareFc(&fc4, &fc5)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc4, fc5): expected negative value, got %d", result)
	}

	result, err = compareFc(&fc4, &fc6)
	if err != nil {
		t.Fatal(err)
	}
	if result != 0 {
		t.Fatalf("compareFc(fc4, fc6): expected 0, got %d", result)
	}

	result, err = compareFc(&fc5, &fc6)
	if err != nil {
		t.Fatal(err)
	}
	if result <= 0 {
		t.Fatalf("compareFc(fc5, fc6): expected positive value, got %d", result)
	}

	result, err = compareFc(&fc4, &fc7)
	if err != nil {
		t.Fatal(err)
	}
	if result >= 0 {
		t.Fatalf("compareFc(fc4, fc7): expected neg value, got %d", result)
	}
}
