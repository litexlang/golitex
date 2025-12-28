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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

func (ie *InferEngine) newTrueEqual(fact *ast.SpecFactStmt) *glob.StmtRet {
	ret := ie.trueEqualFactByCart(fact)
	if ret.IsErr() || ret.IsTrue() {
		return ret
	}

	// 处理 tuple 相等的情况
	ret = ie.trueEqualFactByTuple(fact.Params[0], fact.Params[1])
	if ret.IsErr() || ret.IsTrue() {
		return ret
	}

	// 处理 x = {1, 2, 3} 的情况
	ret = ie.trueEqualFactByListSet(fact.Params[0], fact.Params[1])
	if ret.IsErr() || ret.IsTrue() {
		return ret
	}

	// 处理 x + y = x + z 时，让 y = z 自动成立
	ret = ie.trueEqualFactByLeftIsXAddOrMinusYRightIsXPlusOrMinusZ(fact.Params[0], fact.Params[1])
	if ret.IsErr() || ret.IsTrue() {
		return ret
	}

	// // 如果是 a = b / c 的情况，那就 a * c = b, b * c = 0 自动成立
	// ret = ie.trueEqualFactByFraction(fact.Params[0], fact.Params[1])
	// if ret.IsErr() {
	// 	return ret
	// }

	// // 如果是 b / c = a 的情况，那就 b = a * c, c = b / a 自动成立
	// ret = ie.trueEqualFactByFraction(fact.Params[1], fact.Params[0])
	// if ret.IsErr() {
	// 	return ret
	// }

	// // 如果是 a = b + c 的情况，那就 a - c = b, a - b = c 自动成立
	// ret = ie.trueEqualFactByAddition(fact.Params[0], fact.Params[1])
	// if ret.IsErr() {
	// 	return ret
	// }

	// // 如果是 b + c = a 的情况，那就 a - c = b, a - b = c 自动成立
	// ret = ie.trueEqualFactByAddition(fact.Params[1], fact.Params[0])
	// if ret.IsErr() {
	// 	return ret
	// }

	// // 如果是 a = b - c 的情况，那就 a + c = b, b = a + c 自动成立
	// ret = ie.trueEqualFactBySubtraction(fact.Params[0], fact.Params[1])
	// if ret.IsErr() {
	// 	return ret
	// }

	// // 如果是 b - c = a 的情况，那就 a + c = b, b = a + c 自动成立
	// ret = ie.trueEqualFactBySubtraction(fact.Params[1], fact.Params[0])
	// if ret.IsErr() {
	// 	return ret
	// }

	return glob.NewEmptyStmtTrue()
}

// trueEqualFactByCart handles postprocessing for x = cart(x1, x2, ..., xn)
// It generates:
//   - is_cart(x) fact
//   - dim(x) = len(cart.Params) fact
//   - proj(x, i+1) = cart.Params[i] facts for each i
func (ie *InferEngine) trueEqualFactByCart(fact *ast.SpecFactStmt) *glob.StmtRet {
	cart, ok := fact.Params[1].(*ast.FnObj)
	if !ok || !ast.IsAtomObjAndEqualToStr(cart.FnHead, glob.KeywordCart) {
		return glob.NewEmptyStmtUnknown()
	}

	inferMsgs := []string{}

	// 让 $is_cart(x) 成立
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fact.Params[0]}, glob.BuiltinLine0)
	ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(isCartFact)
	if ret.IsErr() {
		return ret
	}
	inferMsgs = append(inferMsgs, isCartFact.String())

	// dim(x) = len(cart.Params)
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{fact.Params[0]})
	dimValue := ast.Atom(strconv.Itoa(len(cart.Params)))
	dimEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{dimFn, dimValue}, glob.BuiltinLine0)
	ret = ie.EnvMgr.NewFactWithoutCheckingNameDefined(dimEqualFact)
	if ret.IsErr() {
		return ret
	}
	inferMsgs = append(inferMsgs, dimEqualFact.String())

	// proj(x, i+1) = cart.Params[i] for each i
	for i, cartParam := range cart.Params {
		projFn := ast.NewFnObj(ast.Atom(glob.KeywordProj), []ast.Obj{fact.Params[0], ast.Atom(strconv.Itoa(i + 1))})
		projEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{projFn, cartParam}, glob.BuiltinLine0)
		ret = ie.EnvMgr.NewFactWithoutCheckingNameDefined(projEqualFact)
		if ret.IsErr() {
			return ret
		}
		inferMsgs = append(inferMsgs, projEqualFact.String())
	}

	return glob.NewStmtTrueWithInfers((inferMsgs))
}

// trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex handles postprocessing for obj = tuple
// It generates obj[index] = tuple[i] facts for each index
func (ie *InferEngine) trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex(obj ast.Obj, tupleObj ast.Obj) *glob.StmtRet {
	tuple, ok := tupleObj.(*ast.FnObj)
	if !ok || !ast.IsTupleFnObj(tuple) {
		return glob.ErrRet(fmt.Sprintf("expected tuple to be a tuple object, got %T", tupleObj))
	}

	// 让 obj 的每一位对应等于 tuple 的每一位
	for i := range len(tuple.Params) {
		index := i + 1 // 索引从1开始
		indexObj := ast.Atom(strconv.Itoa(index))

		// 创建索引操作: obj[index]
		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordObjAtIndexOpt), []ast.Obj{obj, indexObj})

		// 创建相等事实: obj[index] = tuple[i]
		indexEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{indexedObj, tuple.Params[i]}, glob.BuiltinLine0)
		ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(indexEqualFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

// trueEqualFactByTuple handles postprocessing for tuple equality
// It handles three cases:
//   - (.., …) = (.., ..): tuple = tuple
//   - a = (.., ..): obj = tuple
//   - (.., ..) = a: tuple = obj
func (ie *InferEngine) trueEqualFactByTuple(left ast.Obj, right ast.Obj) *glob.StmtRet {
	inferMsgs := []string{}

	leftTuple, leftIsTuple := left.(*ast.FnObj)
	rightTuple, rightIsTuple := right.(*ast.FnObj)

	if leftIsTuple && rightIsTuple && ast.IsTupleFnObj(leftTuple) && ast.IsTupleFnObj(rightTuple) {
		// 处理 tuple = tuple 的情况，让每一位相等
		ret := ie.trueEqualByLeftAndRightAreBothTuple(leftTuple, rightTuple)
		if ret.IsErr() {
			return ret
		}
		inferMsgs = append(inferMsgs, ret.Infer...)
		return glob.NewStmtTrueWithInfers((inferMsgs))
	} else if rightIsTuple && ast.IsTupleFnObj(rightTuple) {
		// 如果右边是 tuple，左边是对象: a = (1, 2, ..)
		ret := ie.trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex(left, right)
		if ret.IsErr() {
			return ret
		}
		inferMsgs = append(inferMsgs, ret.Infer...)
		return glob.NewStmtTrueWithInfers((inferMsgs))
	} else if leftIsTuple && ast.IsTupleFnObj(leftTuple) {
		// 如果左边是 tuple，右边是对象: (1, 2, ..) = a
		ret := ie.trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex(right, left)
		if ret.IsErr() {
			return ret
		}
		inferMsgs = append(inferMsgs, ret.Infer...)
		return glob.NewStmtTrueWithInfers((inferMsgs))
	}

	return glob.NewEmptyStmtUnknown()
}

func (ie *InferEngine) trueEqualByLeftAndRightAreBothTuple(leftTuple *ast.FnObj, rightTuple *ast.FnObj) *glob.StmtRet {
	// 如果两个 tuple 的长度不同，返回错误
	if len(leftTuple.Params) != len(rightTuple.Params) {
		return glob.ErrRet(fmt.Sprintf("tuple length mismatch: left has %d elements, right has %d elements", len(leftTuple.Params), len(rightTuple.Params)))
	}

	// 让每一位相等
	for i := range len(leftTuple.Params) {
		equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{leftTuple.Params[i], rightTuple.Params[i]}, glob.BuiltinLine0)
		ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(equalFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

// equalFactPostProcess_tupleTuple handles postprocessing for tuple = tuple
// It generates equal facts for each corresponding element
// trueEqualFactByListSet handles postprocessing for x = {1, 2, 3}
// If the right side is a list set (directly or through equal facts), it creates:
//   - An or fact indicating that forall items in the list set, the equals one of the list set elements
//   - count(x) = len(listSet) fact
//   - is_finite_set(x) fact
func (ie *InferEngine) trueEqualFactByListSet(left ast.Obj, right ast.Obj) *glob.StmtRet {
	inferMsgs := []string{}

	// 尝试获取 list set（可能是直接的，也可能是通过 equal facts 得到的）
	listSetObj := ie.EnvMgr.GetListSetEqualToObj(right)
	if listSetObj == nil {
		return glob.NewEmptyStmtUnknown()
	}

	listSetFnObj, ok := listSetObj.(*ast.FnObj)
	if !ok {
		return glob.UnknownRet(fmt.Sprintf("expected list set to be FnObj, got %T", listSetObj))
	}

	// 创建一个 or fact，表示 left 等于 list set 中的某一个元素
	// forall x left => x = left[1] or x = left[2] or ... or x = left[len(left)]
	randomName := ie.EnvMgr.GenerateUndeclaredRandomName()
	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{}, glob.BuiltinLine0)
	for _, param := range listSetFnObj.Params {
		orFact.Facts = append(orFact.Facts, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{ast.Atom(randomName), param}, glob.BuiltinLine0))
	}
	forallFact := ast.NewUniFact([]string{randomName}, []ast.Obj{left}, []ast.FactStmt{}, []ast.FactStmt{orFact}, glob.BuiltinLine0)
	ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(forallFact)
	if ret.IsErr() {
		return glob.NewEmptyStmtUnknown()
	}
	inferMsgs = append(inferMsgs, forallFact.String())

	// count(a) = len
	countFn := ast.NewFnObj(ast.Atom(glob.KeywordCount), []ast.Obj{left})
	countValue := ast.Atom(strconv.Itoa(len(listSetFnObj.Params)))
	countEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{countFn, countValue}, glob.BuiltinLine0)
	ret = ie.EnvMgr.NewFactWithoutCheckingNameDefined(countEqualFact)
	if ret.IsErr() {
		return glob.NewEmptyStmtUnknown()
	}
	inferMsgs = append(inferMsgs, countEqualFact.String())

	// is finite set
	isFiniteFact := ast.NewIsAFiniteSetFact(left, glob.BuiltinLine0)
	ret = ie.EnvMgr.NewFactWithoutCheckingNameDefined(isFiniteFact)
	if ret.IsErr() {
		return glob.NewEmptyStmtUnknown()
	}
	inferMsgs = append(inferMsgs, isFiniteFact.String())
	return glob.NewStmtTrueWithInfers((inferMsgs))
}

// func (ie *InferEngine) trueEqualFactByFraction(left ast.Obj, right ast.Obj) *glob.GlobRet {
// 	// 处理 a = b / c 的情况：推导出 a * c = b
// 	rightFraction, ok := right.(*ast.FnObj)
// 	if ok && rightFraction.HasAtomHeadEqualToStr(glob.KeySymbolSlash) {
// 		if len(rightFraction.Params) != 2 {
// 			return glob.NewEmptyGlobUnknown()
// 		}
// 		numerator := rightFraction.Params[0]   // b
// 		denominator := rightFraction.Params[1] // c

// 		// 推导出 left * denominator = numerator (即 a * c = b)
// 		multiplyObj := ast.NewFnObj(ast.Atom(glob.KeySymbolStar), []ast.Obj{left, denominator})
// 		multiplyEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{multiplyObj, numerator}, glob.BuiltinLine)
// 		ret := ie.EnvMgr.newSpecFactNoInfer(multiplyEqualFact)
// 		if ret.IsErr() {
// 			return ret
// 		}
// 		return glob.NewEmptyGlobTrue()
// 	}
// 	return glob.NewEmptyGlobUnknown()
// }

// func (ie *InferEngine) trueEqualFactByAddition(left ast.Obj, right ast.Obj) *glob.GlobRet {
// 	// 处理 a = b + c 的情况：推导出 a - c = b 和 a - b = c
// 	rightAddition, ok := right.(*ast.FnObj)
// 	if ok && rightAddition.HasAtomHeadEqualToStr(glob.KeySymbolPlus) {
// 		if len(rightAddition.Params) != 2 {
// 			return glob.NewEmptyGlobUnknown()
// 		}
// 		leftOperand := rightAddition.Params[0]  // b
// 		rightOperand := rightAddition.Params[1] // c

// 		// 推导出 left - rightOperand = leftOperand (即 a - c = b)
// 		subtractObj1 := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{left, rightOperand})
// 		subtractEqualFact1 := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{subtractObj1, leftOperand}, glob.BuiltinLine)
// 		ret := ie.EnvMgr.newFactNoInfer(subtractEqualFact1)
// 		if ret.IsErr() {
// 			return ret
// 		}

// 		// 推导出 left - leftOperand = rightOperand (即 a - b = c)
// 		subtractObj2 := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{left, leftOperand})
// 		subtractEqualFact2 := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{subtractObj2, rightOperand}, glob.BuiltinLine)
// 		ret = ie.EnvMgr.newFactNoInfer(subtractEqualFact2)
// 		if ret.IsErr() {
// 			return ret
// 		}

// 		// 推出 a = c + b
// 		addObj3 := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{leftOperand, rightOperand})
// 		addEqualFact3 := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{addObj3, left}, glob.BuiltinLine)
// 		ret = ie.EnvMgr.newFactNoInfer(addEqualFact3)
// 		if ret.IsErr() {
// 			return ret
// 		}

// 		return glob.NewEmptyGlobTrue()
// 	}
// 	return glob.NewEmptyGlobUnknown()
// }

// func (ie *InferEngine) trueEqualFactBySubtraction(left ast.Obj, right ast.Obj) *glob.GlobRet {
// 	// 处理 a = b - c 的情况：推导出 a + c = b 和 b = a + c
// 	rightSubtraction, ok := right.(*ast.FnObj)
// 	if ok && rightSubtraction.HasAtomHeadEqualToStr(glob.KeySymbolMinus) {
// 		if len(rightSubtraction.Params) != 2 {
// 			return glob.NewEmptyGlobUnknown()
// 		}
// 		minuend := rightSubtraction.Params[0]    // b (被减数)
// 		subtrahend := rightSubtraction.Params[1] // c (减数)

// 		// 推导出 left + subtrahend = minuend (即 a + c = b)
// 		addObj := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{left, subtrahend})
// 		addEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{addObj, minuend}, glob.BuiltinLine)
// 		ret := ie.EnvMgr.newFactNoInfer(addEqualFact)
// 		if ret.IsErr() {
// 			return ret
// 		}

// 		// c + a = b
// 		addObj2 := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{subtrahend, left})
// 		addEqualFact2 := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{addObj2, minuend}, glob.BuiltinLine)
// 		ret = ie.EnvMgr.newFactNoInfer(addEqualFact2)
// 		if ret.IsErr() {
// 			return ret
// 		}
// 		return glob.NewEmptyGlobTrue()
// 	}
// 	return glob.NewEmptyGlobUnknown()
// }

func (ie *InferEngine) trueEqualFactByLeftIsXAddOrMinusYRightIsXPlusOrMinusZ(left ast.Obj, right ast.Obj) *glob.StmtRet {
	// 检查 left 是否是 x + y 或 x - y 的形式
	leftFn, leftIsFn := left.(*ast.FnObj)
	if !leftIsFn || len(leftFn.Params) != 2 {
		return glob.NewEmptyStmtUnknown()
	}

	leftHead, leftHeadIsAtom := leftFn.FnHead.(ast.Atom)
	if !leftHeadIsAtom {
		return glob.NewEmptyStmtUnknown()
	}

	leftOp := string(leftHead)
	if leftOp != glob.KeySymbolPlus && leftOp != glob.KeySymbolMinus {
		return glob.NewEmptyStmtUnknown()
	}

	// 检查 right 是否是 x + z 或 x - z 的形式
	rightFn, rightIsFn := right.(*ast.FnObj)
	if !rightIsFn || len(rightFn.Params) != 2 {
		return glob.NewEmptyStmtUnknown()
	}

	rightHead, rightHeadIsAtom := rightFn.FnHead.(ast.Atom)
	if !rightHeadIsAtom {
		return glob.NewEmptyStmtUnknown()
	}

	rightOp := string(rightHead)
	if rightOp != glob.KeySymbolPlus && rightOp != glob.KeySymbolMinus {
		return glob.NewEmptyStmtUnknown()
	}

	// 检查第一参数是否相同（都是 x）
	leftX := leftFn.Params[0]
	rightX := rightFn.Params[0]
	if leftX.String() != rightX.String() {
		return glob.NewEmptyStmtUnknown()
	}

	// 如果操作符相同，直接推导 y = z
	if leftOp == rightOp {
		// x + y = x + z => y = z
		// x - y = x - z => y = z
		y := leftFn.Params[1]
		z := rightFn.Params[1]
		equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{y, z}, glob.BuiltinLine0)
		ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(equalFact)
		if ret.IsErr() {
			return ret
		}
		return glob.NewStmtTrueWithInfers([]string{equalFact.String()})
	}

	// 如果操作符不同，需要特殊处理
	// x + y = x - z => y = -z 或 y + z = 0
	// x - y = x + z => -y = z 或 y + z = 0
	// 我们选择推导 y + z = 0，因为这样更通用
	if leftOp == glob.KeySymbolPlus && rightOp == glob.KeySymbolMinus {
		// x + y = x - z => y + z = 0
		y := leftFn.Params[1]
		z := rightFn.Params[1]
		zero := ast.Atom("0")
		yPlusZ := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{y, z})
		equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{yPlusZ, zero}, glob.BuiltinLine0)
		ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(equalFact)
		if ret.IsErr() {
			return ret
		}
		return glob.NewStmtTrueWithInfers([]string{equalFact.String()})
	}

	if leftOp == glob.KeySymbolMinus && rightOp == glob.KeySymbolPlus {
		// x - y = x + z => y + z = 0
		y := leftFn.Params[1]
		z := rightFn.Params[1]
		zero := ast.Atom("0")
		yPlusZ := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{y, z})
		equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{yPlusZ, zero}, glob.BuiltinLine0)
		ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(equalFact)
		if ret.IsErr() {
			return ret
		}
		return glob.NewStmtTrueWithInfers([]string{equalFact.String()})
	}

	return glob.NewEmptyStmtUnknown()
}
