package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

func (ie *InferEngine) newTrueEqual(fact *ast.SpecFactStmt) glob.GlobRet {
	ret := ie.trueEqualFactByCart(fact)
	if ret.IsErr() {
		return ret
	}

	// 处理 tuple 相等的情况
	ret = ie.trueEqualFactByTuple(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	// 处理 x = {1, 2, 3} 的情况
	ret = ie.trueEqualFactByListSet(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	// 如果是 a = b / c 的情况，那就 a * c = b, b * c = 0 自动成立
	ret = ie.trueEqualFactByFraction(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	// 如果是 b / c = a 的情况，那就 b = a * c, c = b / a 自动成立
	ret = ie.trueEqualFactByFraction(fact.Params[1], fact.Params[0])
	if ret.IsErr() {
		return ret
	}

	// 如果是 a = b + c 的情况，那就 a - c = b, a - b = c 自动成立
	ret = ie.trueEqualFactByAddition(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	// 如果是 b + c = a 的情况，那就 a - c = b, a - b = c 自动成立
	ret = ie.trueEqualFactByAddition(fact.Params[1], fact.Params[0])
	if ret.IsErr() {
		return ret
	}

	// 如果是 a = b - c 的情况，那就 a + c = b, b = a + c 自动成立
	ret = ie.trueEqualFactBySubtraction(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	// 如果是 b - c = a 的情况，那就 a + c = b, b = a + c 自动成立
	ret = ie.trueEqualFactBySubtraction(fact.Params[1], fact.Params[0])
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

// trueEqualFactByCart handles postprocessing for x = cart(x1, x2, ..., xn)
// It generates:
//   - is_cart(x) fact
//   - dim(x) = len(cart.Params) fact
//   - proj(x, i+1) = cart.Params[i] facts for each i
func (ie *InferEngine) trueEqualFactByCart(fact *ast.SpecFactStmt) glob.GlobRet {
	cart, ok := fact.Params[1].(*ast.FnObj)
	if !ok || !ast.IsAtomObjAndEqualToStr(cart.FnHead, glob.KeywordCart) {
		return glob.NewEmptyGlobUnknown()
	}

	// 让 $is_cart(x) 成立
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fact.Params[0]}, glob.BuiltinLine)
	ret := ie.EnvMgr.NewFactWithAtomsDefined(isCartFact)
	if ret.IsErr() {
		return ret
	}

	// dim(x) = len(cart.Params)
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{fact.Params[0]})
	dimValue := ast.Atom(strconv.Itoa(len(cart.Params)))
	dimEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{dimFn, dimValue}, glob.BuiltinLine)
	ret = ie.EnvMgr.NewFactWithAtomsDefined(dimEqualFact)
	if ret.IsErr() {
		return ret
	}

	// proj(x, i+1) = cart.Params[i] for each i
	for i, cartParam := range cart.Params {
		projFn := ast.NewFnObj(ast.Atom(glob.KeywordProj), []ast.Obj{fact.Params[0], ast.Atom(strconv.Itoa(i + 1))})
		projEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{projFn, cartParam}, glob.BuiltinLine)
		ret = ie.EnvMgr.NewFactWithAtomsDefined(projEqualFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

// trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex handles postprocessing for obj = tuple
// It generates obj[index] = tuple[i] facts for each index
func (ie *InferEngine) trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex(obj ast.Obj, tupleObj ast.Obj) glob.GlobRet {
	tuple, ok := tupleObj.(*ast.FnObj)
	if !ok || !ast.IsTupleFnObj(tuple) {
		return glob.ErrRet(fmt.Errorf("expected tuple to be a tuple object, got %T", tupleObj))
	}

	// 让 obj 的每一位对应等于 tuple 的每一位
	for i := range len(tuple.Params) {
		index := i + 1 // 索引从1开始
		indexObj := ast.Atom(strconv.Itoa(index))

		// 创建索引操作: obj[index]
		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordObjAtIndexOpt), []ast.Obj{obj, indexObj})

		// 创建相等事实: obj[index] = tuple[i]
		indexEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{indexedObj, tuple.Params[i]}, glob.BuiltinLine)
		ret := ie.EnvMgr.NewFactWithAtomsDefined(indexEqualFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

// trueEqualFactByTuple handles postprocessing for tuple equality
// It handles three cases:
//   - (.., …) = (.., ..): tuple = tuple
//   - a = (.., ..): obj = tuple
//   - (.., ..) = a: tuple = obj
func (ie *InferEngine) trueEqualFactByTuple(left ast.Obj, right ast.Obj) glob.GlobRet {
	leftTuple, leftIsTuple := left.(*ast.FnObj)
	rightTuple, rightIsTuple := right.(*ast.FnObj)

	if leftIsTuple && rightIsTuple && ast.IsTupleFnObj(leftTuple) && ast.IsTupleFnObj(rightTuple) {
		// 处理 tuple = tuple 的情况，让每一位相等
		return ie.trueEqualByLeftAndRightAreBothTuple(leftTuple, rightTuple)
	} else if rightIsTuple && ast.IsTupleFnObj(rightTuple) {
		// 如果右边是 tuple，左边是对象: a = (1, 2, ..)
		return ie.trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex(left, right)
	} else if leftIsTuple && ast.IsTupleFnObj(leftTuple) {
		// 如果左边是 tuple，右边是对象: (1, 2, ..) = a
		return ie.trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex(right, left)
	}

	return glob.NewEmptyGlobTrue()
}

func (ie *InferEngine) trueEqualByLeftAndRightAreBothTuple(leftTuple *ast.FnObj, rightTuple *ast.FnObj) glob.GlobRet {
	// 如果两个 tuple 的长度不同，返回错误
	if len(leftTuple.Params) != len(rightTuple.Params) {
		return glob.ErrRet(fmt.Errorf("tuple length mismatch: left has %d elements, right has %d elements", len(leftTuple.Params), len(rightTuple.Params)))
	}

	// 让每一位相等
	for i := range len(leftTuple.Params) {
		equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{leftTuple.Params[i], rightTuple.Params[i]}, glob.BuiltinLine)
		ret := ie.EnvMgr.NewFactWithAtomsDefined(equalFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

// equalFactPostProcess_tupleTuple handles postprocessing for tuple = tuple
// It generates equal facts for each corresponding element
// trueEqualFactByListSet handles postprocessing for x = {1, 2, 3}
// If the right side is a list set (directly or through equal facts), it creates:
//   - An or fact indicating that x equals one of the list set elements
//   - count(x) = len(listSet) fact
//   - is_finite_set(x) fact
func (ie *InferEngine) trueEqualFactByListSet(left ast.Obj, right ast.Obj) glob.GlobRet {
	// 尝试获取 list set（可能是直接的，也可能是通过 equal facts 得到的）
	listSetObj := ie.EnvMgr.GetListSetEqualToObj(right)
	if listSetObj == nil {
		return glob.NewEmptyGlobTrue()
	}

	listSetFnObj, ok := listSetObj.(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("expected list set to be FnObj, got %T", listSetObj))
	}

	// 创建一个 or fact，表示 left 等于 list set 中的某一个元素
	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{}, glob.BuiltinLine)
	for _, param := range listSetFnObj.Params {
		orFact.Facts = append(orFact.Facts, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, param}, glob.BuiltinLine))
	}
	ret := ie.EnvMgr.NewFactWithAtomsDefined(orFact)
	if ret.IsErr() {
		return ret
	}

	// count(a) = len
	countFn := ast.NewFnObj(ast.Atom(glob.KeywordCount), []ast.Obj{left})
	countValue := ast.Atom(strconv.Itoa(len(listSetFnObj.Params)))
	countEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{countFn, countValue}, glob.BuiltinLine)
	ret = ie.EnvMgr.NewFactWithAtomsDefined(countEqualFact)
	if ret.IsErr() {
		return ret
	}

	// is finite set
	isFiniteFact := ast.NewIsAFiniteSetFact(left, glob.BuiltinLine)
	return ie.EnvMgr.NewFactWithAtomsDefined(isFiniteFact)
}

func (ie *InferEngine) trueEqualFactByFraction(left ast.Obj, right ast.Obj) glob.GlobRet {
	// 处理 a = b / c 的情况：推导出 a * c = b
	rightFraction, ok := right.(*ast.FnObj)
	if ok && rightFraction.HasAtomHeadEqualToStr(glob.KeySymbolSlash) {
		if len(rightFraction.Params) != 2 {
			return glob.NewEmptyGlobUnknown()
		}
		numerator := rightFraction.Params[0]   // b
		denominator := rightFraction.Params[1] // c

		// 推导出 left * denominator = numerator (即 a * c = b)
		multiplyObj := ast.NewFnObj(ast.Atom(glob.KeySymbolStar), []ast.Obj{left, denominator})
		multiplyEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{multiplyObj, numerator}, glob.BuiltinLine)
		ret := ie.EnvMgr.newSpecFactNoInfer(multiplyEqualFact)
		if ret.IsErr() {
			return ret
		}
		return glob.NewEmptyGlobTrue()
	}
	return glob.NewEmptyGlobUnknown()
}

func (ie *InferEngine) trueEqualFactByAddition(left ast.Obj, right ast.Obj) glob.GlobRet {
	// 处理 a = b + c 的情况：推导出 a - c = b 和 a - b = c
	rightAddition, ok := right.(*ast.FnObj)
	if ok && rightAddition.HasAtomHeadEqualToStr(glob.KeySymbolPlus) {
		if len(rightAddition.Params) != 2 {
			return glob.NewEmptyGlobUnknown()
		}
		leftOperand := rightAddition.Params[0]  // b
		rightOperand := rightAddition.Params[1] // c

		// 推导出 left - rightOperand = leftOperand (即 a - c = b)
		subtractObj1 := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{left, rightOperand})
		subtractEqualFact1 := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{subtractObj1, leftOperand}, glob.BuiltinLine)
		ret := ie.EnvMgr.newFactNoInfer(subtractEqualFact1)
		if ret.IsErr() {
			return ret
		}

		// 推导出 left - leftOperand = rightOperand (即 a - b = c)
		subtractObj2 := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{left, leftOperand})
		subtractEqualFact2 := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{subtractObj2, rightOperand}, glob.BuiltinLine)
		ret = ie.EnvMgr.newFactNoInfer(subtractEqualFact2)
		if ret.IsErr() {
			return ret
		}

		// 推出 a = c + b
		addObj3 := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{leftOperand, rightOperand})
		addEqualFact3 := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{addObj3, left}, glob.BuiltinLine)
		ret = ie.EnvMgr.newFactNoInfer(addEqualFact3)
		if ret.IsErr() {
			return ret
		}

		return glob.NewEmptyGlobTrue()
	}
	return glob.NewEmptyGlobUnknown()
}

func (ie *InferEngine) trueEqualFactBySubtraction(left ast.Obj, right ast.Obj) glob.GlobRet {
	// 处理 a = b - c 的情况：推导出 a + c = b 和 b = a + c
	rightSubtraction, ok := right.(*ast.FnObj)
	if ok && rightSubtraction.HasAtomHeadEqualToStr(glob.KeySymbolMinus) {
		if len(rightSubtraction.Params) != 2 {
			return glob.NewEmptyGlobUnknown()
		}
		minuend := rightSubtraction.Params[0]    // b (被减数)
		subtrahend := rightSubtraction.Params[1] // c (减数)

		// 推导出 left + subtrahend = minuend (即 a + c = b)
		addObj := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{left, subtrahend})
		addEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{addObj, minuend}, glob.BuiltinLine)
		ret := ie.EnvMgr.newFactNoInfer(addEqualFact)
		if ret.IsErr() {
			return ret
		}

		// c + a = b
		addObj2 := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{subtrahend, left})
		addEqualFact2 := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{addObj2, minuend}, glob.BuiltinLine)
		ret = ie.EnvMgr.newFactNoInfer(addEqualFact2)
		if ret.IsErr() {
			return ret
		}
		return glob.NewEmptyGlobTrue()
	}
	return glob.NewEmptyGlobUnknown()
}
