package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

func (ie *InferenceEngine) newTrueEqual(fact *ast.SpecFactStmt) glob.GlobRet {
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

	return glob.NewEmptyGlobTrue()
}

// trueEqualFactByCart handles postprocessing for x = cart(x1, x2, ..., xn)
// It generates:
//   - is_cart(x) fact
//   - dim(x) = len(cart.Params) fact
//   - proj(x, i+1) = cart.Params[i] facts for each i
func (ie *InferenceEngine) trueEqualFactByCart(fact *ast.SpecFactStmt) glob.GlobRet {
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
func (ie *InferenceEngine) trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex(obj ast.Obj, tupleObj ast.Obj) glob.GlobRet {
	tuple, ok := tupleObj.(*ast.FnObj)
	if !ok || !ast.IsTupleFnObj(tuple) {
		return glob.ErrRet(fmt.Errorf("expected tuple to be a tuple object, got %T", tupleObj))
	}

	// 让 obj 的每一位对应等于 tuple 的每一位
	for i := range len(tuple.Params) {
		index := i + 1 // 索引从1开始
		indexObj := ast.Atom(strconv.Itoa(index))

		// 创建索引操作: obj[index]
		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordIndexOpt), []ast.Obj{obj, indexObj})

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
func (ie *InferenceEngine) trueEqualFactByTuple(left ast.Obj, right ast.Obj) glob.GlobRet {
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

func (ie *InferenceEngine) trueEqualByLeftAndRightAreBothTuple(leftTuple *ast.FnObj, rightTuple *ast.FnObj) glob.GlobRet {
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
func (ie *InferenceEngine) trueEqualFactByListSet(left ast.Obj, right ast.Obj) glob.GlobRet {
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
