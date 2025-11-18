// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_comparator

import (
	ast "golitex/ast"
	glob "golitex/glob"
	parser "golitex/parser"
)

func IsNumExprObjThenSimplify(obj ast.Obj) ast.Obj {
	return parser.IsNumExprObj_SimplifyIt(obj)
}

func CmpBy_Literally_NumLit_PolynomialArith(left, right ast.Obj) (bool, string, error) {
	// case 0: 按字面量来比较。这必须在比较div和比较polynomial之前，因为可能比较的是 * 和 *，即比较两个函数是不是一样。这种函数的比较，跑到div和polynomial就会出问题，因为在那些地方*都会被当成有参数的东西
	ok, err := cmpObjLiterally(left, right)
	if err != nil {
		return false, "", err
	}
	if ok {
		return true, "the same", nil
	}

	areNumLit, areEqual, err := NumLitEqual_ByEval(left, right)
	if err != nil {
		return false, "", err
	}
	if areNumLit && areEqual {
		return true, "builtin calculation", nil
	}

	leftStr := left.String()
	rightStr := right.String()

	cmp := cmpArith_ByBIR(leftStr, rightStr)
	if cmp {
		return true, "The two polynomials become the same after simplification.", nil
	}

	return false, "", nil
}

func IsNumLitObj(obj ast.Obj) bool {
	_, ok, err := ast.MakeObjIntoNumLitExpr(obj)
	if err != nil {
		return false
	}
	return ok
}

func NumLitEqual_ByEval(left, right ast.Obj) (bool, bool, error) {
	leftAsNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(left)
	if err != nil {
		return false, false, err
	}
	if !ok {
		return false, false, nil
	}

	rightAsNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(right)
	if err != nil {
		return false, false, err
	}
	if !ok {
		return false, false, nil
	}

	areEqual, err := glob.NumLitExprEqual_ByEval(leftAsNumLitExpr, rightAsNumLitExpr)
	return true, areEqual, err
}

func SliceObjAllEqualToGivenObjBuiltinRule(valuesToBeComped *[]ast.Obj, objToComp ast.Obj) (bool, error) {
	for _, equalObj := range *valuesToBeComped {
		ok, _, err := CmpBy_Literally_NumLit_PolynomialArith(equalObj, objToComp)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}
