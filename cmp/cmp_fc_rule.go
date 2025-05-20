// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_comparator

import (
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

func CmpFcAsStr(left, right ast.Fc) bool {
	return left.String() == right.String()
}

func CmpFcRule(left, right ast.Fc) (bool, error) {
	// 先验证是不是Number，后验证rule，居然让runtime速度提高了1倍。。。
	ok, err := BuiltinFcEqualRule(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = cmpFcAtomLitFcFnRule(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

// 先确定left，right都是builtin fc，然后按builtin rule来验证他们相等
func BuiltinFcEqualRule(left, right ast.Fc) (bool, error) {
	// case 0: 比较 number expr
	cmp := cmpArithmeticExpr(left, right)
	if cmp == 0 {
		return true, nil
	}

	// Case1: 二者都是 Number 上进行+-*/^
	ok, err := cmpNumLitExpr(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func cmpArithmeticExpr(left, right ast.Fc) int {
	if orderedLeft, ok, err := ast.IsArithmeticExpr_OrderIt(left); err != nil {
		return -1
	} else if !ok {
		return -1
	} else {
		if orderedRight, ok, err := ast.IsArithmeticExpr_OrderIt(right); err != nil {
			return -1
		} else if !ok {
			return -1
		} else {
			if len(orderedLeft) != len(orderedRight) {
				return -1
			}
			for i := range orderedLeft {
				cmp := strings.Compare(orderedLeft[i].String(), orderedRight[i].String())
				if cmp != 0 {
					return cmp
				}
			}
			return 0
		}
	}
}

// 之所以叫 Expr，因为可能含有运算符+-*/这样的
func cmpNumLitExpr(left, right ast.Fc) (bool, error) {
	leftAsNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(left)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightAsNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(right)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return glob.NumLitExprEqual(leftAsNumLitExpr, rightAsNumLitExpr)
}

func SliceFcAllEqualToGivenFcBuiltinRule(valuesToBeComped *[]ast.Fc, fcToComp ast.Fc) (bool, error) {
	for _, equalFc := range *valuesToBeComped {
		ok, err := CmpFcRule(equalFc, fcToComp)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}
