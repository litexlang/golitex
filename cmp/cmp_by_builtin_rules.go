// Copyright Jiachen Shen.
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
)

// isArithmeticExpr 检查 obj 是否是四则运算表达式（+、-、*、/）
// 递归检查：数字字面量、一元负号、二元四则运算
func isArithmeticExpr(obj ast.Obj) bool {
	// 检查是否是数字字面量原子
	if _, ok := ast.IsNumLitAtomObj(obj); ok {
		return true
	}

	// 检查是否是 FnObj
	fnObj, ok := obj.(*ast.FnObj)
	if !ok {
		return false
	}

	// 检查 FnHead 是否是 Atom
	fnHead, ok := fnObj.FnHead.(ast.Atom)
	if !ok {
		return false
	}

	op := string(fnHead)

	// 检查一元负号：-x
	if op == glob.KeySymbolMinus && len(fnObj.Params) == 1 {
		return isArithmeticExpr(fnObj.Params[0])
	}

	// 检查二元四则运算：+、-、*、/
	isArithmeticOp := op == glob.KeySymbolPlus || op == glob.KeySymbolMinus ||
		op == glob.KeySymbolStar || op == glob.KeySymbolSlash

	if !isArithmeticOp {
		return false
	}

	// 二元运算必须有两个参数
	if len(fnObj.Params) != 2 {
		return false
	}

	// 递归检查两个参数是否也是算术表达式
	return isArithmeticExpr(fnObj.Params[0]) && isArithmeticExpr(fnObj.Params[1])
}

func IsNumExprObjThenSimplify(obj ast.Obj) ast.Obj {
	// 如果不满足四则运算表达式的结构，返回 nil
	if !isArithmeticExpr(obj) {
		return nil
	}

	// 使用 ast.MakeObjIntoNumLitExpr 来转换为 NumLitExpr 并计算
	numLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(obj)
	if err != nil || !ok {
		return nil
	}

	evaluatedStr, evaluated, err := numLitExpr.EvalNumLitExpr()
	if err != nil || !evaluated {
		return nil
	}

	// 由于不能使用 parser，返回原对象（或者可以返回一个简单的数字原子）
	// 但这里需要将 evaluatedStr 转换为 ast.Obj
	// 如果 evaluatedStr 是纯数字，可以创建一个 Atom
	// 否则返回原对象表示无法简化
	if glob.IsNumLitStr(evaluatedStr) {
		return ast.Atom(evaluatedStr)
	}

	return nil
}

func CmpBy_Literally_NumLit_PolynomialArith(left, right ast.Obj) (bool, string, error) {
	// case 0: 按字面量来比较。这必须在比较div和比较polynomial之前，因为可能比较的是 * 和 *，即比较两个函数是不是一样。这种函数的比较，跑到div和polynomial就会出问题，因为在那些地方*都会被当成有参数的东西
	ok, err := cmpObjLiterally(left, right)
	if err != nil {
		return false, "", err
	}
	if ok {
		return true, "they are literally the same", nil
	}

	areNumLit, areEqual, err := NumLitEqual_ByEval(left, right)
	if err != nil {
		return false, "", err
	}
	if areNumLit && areEqual {
		return true, "calculation", nil
	}

	leftStr := left.String()
	rightStr := right.String()

	cmp := cmpArith_ByBIR(leftStr, rightStr)
	if cmp {
		return true, "The two polynomials become the same after simplification.", nil
	}

	return false, "", nil
}

func IsNumExprLitObj(obj ast.Obj) bool {
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
