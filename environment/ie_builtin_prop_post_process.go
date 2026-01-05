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
	ast "golitex/ast"
	glob "golitex/glob"
)

// BuiltinPropExceptTrueEqual handles postprocessing for builtin properties except equality
func (ie *InferEngine) BuiltinPropExceptTrueEqual(fact *ast.SpecFactStmt) *glob.ShortRet {
	if ast.IsTrueSpecFactWithPropName(fact, glob.KeywordIn) {
		return ie.trueInFact(fact)
	}

	if ast.IsFalseSpecFactWithPropName(fact, glob.KeySymbolEqual) {
		return ie.falseEqualFact(fact)
	}

	if ast.IsTrueSpecFactWithPropName(fact, glob.KeySymbolGreater) {
		if fact.Params[1].String() == "0" {
			return ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(fact)
		} else {
			return ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsNotZero(fact)
		}
	}

	if ast.IsTrueSpecFactWithPropName(fact, glob.KeySymbolLargerEqual) {
		if fact.Params[1].String() == "0" {
			return ie.builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsZero(fact)
		} else {
			return ie.builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsNotZero(fact)
		}
	}

	if ast.IsTrueSpecFactWithPropName(fact, glob.KeySymbolLess) {
		if fact.Params[1].String() == "0" {
			return ie.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(fact)
		} else {
			return ie.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsNotZero(fact)
		}
	}

	if ast.IsTrueSpecFactWithPropName(fact, glob.KeySymbolLessEqual) {
		if fact.Params[1].String() == "0" {
			return ie.builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsZero(fact)
		} else {
			return ie.builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(fact)
		}
	}

	if ast.IsTrueSpecFactWithPropName(fact, glob.KeywordEqualSet) {
		ret := ie.equalSetFactPostProcess(fact)
		return ret
	}

	if ast.IsTrueSpecFactWithPropName(fact, glob.KeywordEqualTuple) {
		ret := ie.equalTupleFactPostProcess(fact)
		// Inherit derived facts from equal tuple post-processing
		return ret
	}

	if ast.IsTrueSpecFactWithPropName(fact, glob.KeywordSubsetOf) {
		ret := ie.subsetOfFactPostProcess(fact)
		// Inherit derived facts from subset_of post-processing
		return ret
	}

	// if ast.IsTrueSpecFactWithPropName(fact, glob.KeywordIsNonEmptyWithItem) {
	// 	ret := ie.isNonEmptyWithItemFactPostProcess(fact)
	// 	return ret
	// }

	// if ast.IsTrueSpecFactWithPropName(fact, glob.KeywordNotEqualSet) {
	// 	ret := ie.notEqualSetFactPostProcess(fact)
	// 	return ret
	// }

	return glob.NewEmptyShortUnknownRet()
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	// x != 0 store spec Mem
	notEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, notEqualZeroFact.String())

	// x >= 0
	greaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, greaterEqualZeroFact.String())

	// not x <= 0
	lessEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(lessEqualZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, lessEqualZeroFact.String())

	// -x: -1 * x
	minusX := ast.NegateObj(fact.Params[0])

	// x > -x
	greaterThanMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterThanMinusXFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, greaterThanMinusXFact.String())

	// -x < 0
	minusXLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{minusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(minusXLessThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, minusXLessThanZeroFact.String())

	// 1/x > 0
	oneDivX := ast.NewFnObj(ast.Atom(glob.KeySymbolSlash), []ast.Obj{ast.Atom("1"), fact.Params[0]})
	oneDivXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{oneDivX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(oneDivXGreaterThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, oneDivXGreaterThanZeroFact.String())

	// x^2 > 0
	xSquared := ast.NewFnObj(ast.Atom(glob.KeySymbolPower), []ast.Obj{fact.Params[0], ast.Atom("2")})
	xSquaredGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{xSquared, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(xSquaredGreaterThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, xSquaredGreaterThanZeroFact.String())

	// sqrt(x) > 0
	sqrtX := ast.NewFnObj(ast.Atom("sqrt"), []ast.Obj{fact.Params[0]})
	sqrtXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{sqrtX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(sqrtXGreaterThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, sqrtXGreaterThanZeroFact.String())

	if len(derivedFacts) > 0 {
		return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
	}
	return glob.NewEmptyShortTrueRet()
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsZero(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	// abs(x) = x
	absX := ast.NewFnObj(ast.Atom("abs"), []ast.Obj{fact.Params[0]})
	absXEqualXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{absX, fact.Params[0]}, fact.Line)
	ret := ie.storeSpecFactInMemAndCollect(absXEqualXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// -x: -1 * x
	minusX := ast.NewFnObj(ast.Atom(glob.KeySymbolStar), []ast.Obj{ast.Atom("-1"), fact.Params[0]})

	// x >= -x
	greaterEqualMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	retShort := ie.storeSpecFactInMemAndCollect(greaterEqualMinusXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// sqrt(x) >= 0
	sqrtX := ast.NewFnObj(ast.Atom("sqrt"), []ast.Obj{fact.Params[0]})
	sqrtXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{sqrtX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(sqrtXGreaterEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	// x != 0 store spec Mem
	notEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	retShort := ie.storeSpecFactInMemAndCollect(notEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x <= 0
	lessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(lessEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// not x >= 0
	greaterEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(greaterEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// -x: -1 * x
	minusX := ast.NewFnObj(ast.Atom(glob.KeySymbolStar), []ast.Obj{ast.Atom("-1"), fact.Params[0]})

	// x < -x
	lessThanMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(lessThanMinusXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// -x > 0
	minusXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{minusX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(minusXGreaterThanZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// 1/x < 0
	oneDivX := ast.NewFnObj(ast.Atom(glob.KeySymbolSlash), []ast.Obj{ast.Atom("1"), fact.Params[0]})
	oneDivXLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{oneDivX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(oneDivXLessThanZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x^2 > 0
	xSquared := ast.NewFnObj(ast.Atom(glob.KeySymbolPower), []ast.Obj{fact.Params[0], ast.Atom("2")})
	xSquaredGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{xSquared, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(xSquaredGreaterThanZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsZero(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	// abs(x) = -x
	absX := ast.NewFnObj(ast.Atom("abs"), []ast.Obj{fact.Params[0]})
	minusX := ast.NegateObj(fact.Params[0])
	absXEqualMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{absX, minusX}, fact.Line)
	retShort := ie.storeSpecFactInMemAndCollect(absXEqualMinusXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x <= -x
	lessEqualMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(lessEqualMinusXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// -x >= 0
	minusXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{minusX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(minusXGreaterEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsNotZero(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	// x > c (c != 0)
	// x != c
	notEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	retShort := ie.storeSpecFactInMemAndCollect(notEqualCFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x >= c
	greaterEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(greaterEqualCFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// not x <= c
	lessEqualCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(lessEqualCFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c < x (等价表述)
	cLessThanXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cLessThanXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// not c >= x
	cGreaterEqualXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cGreaterEqualXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x - c > 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(xMinusCGreaterThanZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x - c >= 0
	xMinusCGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(xMinusCGreaterEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c - x < 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cMinusXLessThanZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c - x <= 0
	cMinusXLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cMinusXLessEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsNotZero(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	// x >= c (c != 0)
	// not x < c
	lessCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	retShort := ie.storeSpecFactInMemAndCollect(lessCFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c <= x (等价表述)
	cLessEqualXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cLessEqualXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// not c > x
	cGreaterXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cGreaterXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x - c >= 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(xMinusCGreaterEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c - x <= 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cMinusXLessEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsNotZero(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	// x < c (c != 0)
	// x != c
	notEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	retShort := ie.storeSpecFactInMemAndCollect(notEqualCFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x <= c
	lessEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(lessEqualCFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// not x >= c
	greaterEqualCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(greaterEqualCFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c > x (等价表述)
	cGreaterThanXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cGreaterThanXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// not c <= x
	cLessEqualXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cLessEqualXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x - c < 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(xMinusCLessThanZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x - c <= 0
	xMinusCLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(xMinusCLessEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c - x > 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cMinusXGreaterThanZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c - x >= 0
	cMinusXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cMinusXGreaterEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	// x <= c (c != 0)
	// not x > c
	greaterCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	retShort := ie.storeSpecFactInMemAndCollect(greaterCFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c >= x (等价表述)
	cGreaterEqualXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cGreaterEqualXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// not c < x
	cLessXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cLessXFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// x - c <= 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(xMinusCLessEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	// c - x >= 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	retShort = ie.storeSpecFactInMemAndCollect(cMinusXGreaterEqualZeroFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) subsetOfFactPostProcess(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}
	// 生成出来一个 random variable t
	obj := ie.EnvMgr.GenerateUndeclaredRandomName()

	forallFact := ast.NewUniFact([]string{obj}, []ast.Obj{fact.Params[0]}, []ast.FactStmt{}, []ast.FactStmt{ast.NewInFact(obj, fact.Params[1])}, fact.Line)

	ret := ie.EnvMgr.newUniFact(forallFact)

	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	derivedFacts = append(derivedFacts, forallFact.String())

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) falseEqualFact(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	// x - y != 0
	notEqualFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]}), ast.Atom("0")}, fact.Line)
	retShort := ie.storeSpecFactInMemAndCollect(notEqualFact, &derivedFacts)
	if retShort.IsErr() {
		return retShort
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// func (ie *InferEngine) isNonEmptyWithItemFactPostProcess(fact *ast.SpecFactStmt) *glob.ShortRet {
// 	derivedFacts := []string{}

// 	// fact.Params[0] 非空
// 	isNonEmptyFact := ast.NewIsANonEmptySetFact(fact.Params[0], fact.Line)
// 	retShort := ie.storeSpecFactInMemAndCollect(isNonEmptyFact, &derivedFacts)
// 	if retShort.IsErr() {
// 		return retShort
// 	}

// 	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
// }

// func (ie *InferEngine) notEqualSetFactPostProcess(fact *ast.SpecFactStmt) *glob.ShortRet {
// 	derivedFacts := []string{}

// 	// x != y
// 	notEqualFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
// 	retShort := ie.storeSpecFactInMemAndCollect(notEqualFact, &derivedFacts)
// 	if retShort.IsErr() {
// 		return retShort
// 	}

// 	// exist z x st not z $in y or exist z y st not z $in x
// 	randomName := ie.EnvMgr.GenerateUndeclaredRandomName()
// 	existZInXStNotZInYFact := ast.NewExistStFactStruct(ast.TrueExist_St, ast.Atom(glob.KeywordIn), false, []string{(randomName)}, []ast.Obj{fact.Params[0]}, []ast.Obj{ast.Atom(randomName), fact.Params[1]}, fact.Line)
// 	existZInYStNotZInXFact := ast.NewExistStFactStruct(ast.TrueExist_St, ast.Atom(glob.KeywordIn), false, []string{(randomName)}, []ast.Obj{fact.Params[1]}, []ast.Obj{ast.Atom(randomName), fact.Params[0]}, fact.Line)
// 	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{existZInXStNotZInYFact.ToExistStFact(), existZInYStNotZInXFact.ToExistStFact()}, fact.Line)

// 	stmtRet := ie.EnvMgr.newOrFact(orFact)
// 	if stmtRet.IsNotTrue() {
// 		return glob.NewShortRet(glob.StmtRetTypeError, []string{})
// 	}

// 	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
// }
