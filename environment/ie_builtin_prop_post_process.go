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

// storeSpecFactInMemAndCollect collects the fact string for derived facts tracking
func (ie *InferEngine) storeSpecFactInMemAndCollect(fact *ast.SpecFactStmt, derivedFacts *[]string) *glob.GlobRet {
	ret := ie.EnvMgr.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}
	*derivedFacts = append(*derivedFacts, fact.String())
	return glob.NewEmptyGlobTrue()
}

// BuiltinPropExceptTrueEqual handles postprocessing for builtin properties except equality
func (ie *InferEngine) BuiltinPropExceptTrueEqual(fact *ast.SpecFactStmt) *glob.GlobRet {
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

	if ast.IsTrueSpecFactWithPropName(fact, glob.KeywordIsNonEmptyWithItem) {
		ret := ie.isNonEmptyWithItemFactPostProcess(fact)
		return ret
	}

	return glob.NewEmptyGlobUnknown()
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}

	// x != 0 store spec Mem
	notEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, notEqualZeroFact.String())

	// x >= 0
	greaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, greaterEqualZeroFact.String())

	// not x <= 0
	lessEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(lessEqualZeroFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, lessEqualZeroFact.String())

	// -x: -1 * x
	minusX := ast.NegateObj(fact.Params[0])

	// x > -x
	greaterThanMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterThanMinusXFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, greaterThanMinusXFact.String())

	// -x < 0
	minusXLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{minusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(minusXLessThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, minusXLessThanZeroFact.String())

	// 1/x > 0
	oneDivX := ast.NewFnObj(ast.Atom(glob.KeySymbolSlash), []ast.Obj{ast.Atom("1"), fact.Params[0]})
	oneDivXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{oneDivX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(oneDivXGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, oneDivXGreaterThanZeroFact.String())

	// x^2 > 0
	xSquared := ast.NewFnObj(ast.Atom(glob.KeySymbolPower), []ast.Obj{fact.Params[0], ast.Atom("2")})
	xSquaredGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{xSquared, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(xSquaredGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, xSquaredGreaterThanZeroFact.String())

	// sqrt(x) > 0
	sqrtX := ast.NewFnObj(ast.Atom("sqrt"), []ast.Obj{fact.Params[0]})
	sqrtXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{sqrtX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(sqrtXGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, sqrtXGreaterThanZeroFact.String())

	if len(derivedFacts) > 0 {
		return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
	}
	return glob.NewEmptyGlobTrue()
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsZero(fact *ast.SpecFactStmt) *glob.GlobRet {
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
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(greaterEqualMinusXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// sqrt(x) >= 0
	sqrtX := ast.NewFnObj(ast.Atom("sqrt"), []ast.Obj{fact.Params[0]})
	sqrtXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{sqrtX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(sqrtXGreaterEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}

	// x != 0 store spec Mem
	notEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMemAndCollect(notEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x <= 0
	lessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(lessEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// not x >= 0
	greaterEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(greaterEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// -x: -1 * x
	minusX := ast.NewFnObj(ast.Atom(glob.KeySymbolStar), []ast.Obj{ast.Atom("-1"), fact.Params[0]})

	// x < -x
	lessThanMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(lessThanMinusXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// -x > 0
	minusXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{minusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(minusXGreaterThanZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// 1/x < 0
	oneDivX := ast.NewFnObj(ast.Atom(glob.KeySymbolSlash), []ast.Obj{ast.Atom("1"), fact.Params[0]})
	oneDivXLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{oneDivX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(oneDivXLessThanZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x^2 > 0
	xSquared := ast.NewFnObj(ast.Atom(glob.KeySymbolPower), []ast.Obj{fact.Params[0], ast.Atom("2")})
	xSquaredGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{xSquared, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(xSquaredGreaterThanZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsZero(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}

	// abs(x) = -x
	absX := ast.NewFnObj(ast.Atom("abs"), []ast.Obj{fact.Params[0]})
	minusX := ast.NegateObj(fact.Params[0])
	absXEqualMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{absX, minusX}, fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMemAndCollect(absXEqualMinusXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x <= -x
	lessEqualMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(lessEqualMinusXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// -x >= 0
	minusXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{minusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(minusXGreaterEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsNotZero(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}

	// x > c (c != 0)
	// x != c
	notEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMemAndCollect(notEqualCFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x >= c
	greaterEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(greaterEqualCFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// not x <= c
	lessEqualCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(lessEqualCFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c < x (等价表述)
	cLessThanXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cLessThanXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// not c >= x
	cGreaterEqualXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cGreaterEqualXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x - c > 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(xMinusCGreaterThanZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x - c >= 0
	xMinusCGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(xMinusCGreaterEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c - x < 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cMinusXLessThanZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c - x <= 0
	cMinusXLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cMinusXLessEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsNotZero(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}

	// x >= c (c != 0)
	// not x < c
	lessCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMemAndCollect(lessCFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c <= x (等价表述)
	cLessEqualXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cLessEqualXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// not c > x
	cGreaterXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cGreaterXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x - c >= 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(xMinusCGreaterEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c - x <= 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cMinusXLessEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsNotZero(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}

	// x < c (c != 0)
	// x != c
	notEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMemAndCollect(notEqualCFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x <= c
	lessEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(lessEqualCFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// not x >= c
	greaterEqualCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(greaterEqualCFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c > x (等价表述)
	cGreaterThanXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cGreaterThanXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// not c <= x
	cLessEqualXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cLessEqualXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x - c < 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(xMinusCLessThanZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x - c <= 0
	xMinusCLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(xMinusCLessEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c - x > 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cMinusXGreaterThanZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c - x >= 0
	cMinusXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cMinusXGreaterEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}

func (ie *InferEngine) builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}

	// x <= c (c != 0)
	// not x > c
	greaterCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMemAndCollect(greaterCFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c >= x (等价表述)
	cGreaterEqualXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cGreaterEqualXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// not c < x
	cLessXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cLessXFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// x - c <= 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(xMinusCLessEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	// c - x >= 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMemAndCollect(cMinusXGreaterEqualZeroFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}

func (ie *InferEngine) subsetOfFactPostProcess(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}
	// 生成出来一个 random variable t
	obj := ie.EnvMgr.GenerateUndeclaredRandomName()

	forallFact := ast.NewUniFact([]string{obj}, []ast.Obj{fact.Params[0]}, []ast.FactStmt{}, []ast.FactStmt{ast.NewInFact(obj, fact.Params[1])}, fact.Line)

	ret := ie.EnvMgr.newUniFact(forallFact)

	if ret.IsErr() {
		return ret
	}

	derivedFacts = append(derivedFacts, forallFact.String())

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}

func (ie *InferEngine) falseEqualFact(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}

	// x - y != 0
	notEqualFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]}), ast.Atom("0")}, fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMemAndCollect(notEqualFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}

func (ie *InferEngine) isNonEmptyWithItemFactPostProcess(fact *ast.SpecFactStmt) *glob.GlobRet {
	derivedFacts := []string{}

	// fact.Params[0] 非空
	isNonEmptyFact := ast.NewIsANonEmptySetFact(fact.Params[0], fact.Line)
	ret := ie.EnvMgr.storeSpecFactInMemAndCollect(isNonEmptyFact, &derivedFacts)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue(glob.InferMsgs(derivedFacts))
}
