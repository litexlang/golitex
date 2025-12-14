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

package litex_env

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

// BuiltinPropExceptEqualPostProcess handles postprocessing for builtin properties except equality
func (env *Env) BuiltinPropExceptEqualPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if fact.PropName == glob.KeywordIn {
		return env.inFactPostProcess(fact)
	}

	if fact.PropName == glob.KeySymbolGreater {
		if fact.Params[1].String() == "0" {
			return env.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(fact)
		} else {
			return env.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsNotZero(fact)
		}
	}

	if fact.PropName == glob.KeySymbolLargerEqual {
		if fact.Params[1].String() == "0" {
			return env.builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsZero(fact)
		} else {
			return env.builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsNotZero(fact)
		}
	}

	if fact.PropName == glob.KeySymbolLess {
		if fact.Params[1].String() == "0" {
			return env.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(fact)
		} else {
			return env.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsNotZero(fact)
		}
	}

	if fact.PropName == glob.KeySymbolLessEqual {
		if fact.Params[1].String() == "0" {
			return env.builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsZero(fact)
		} else {
			return env.builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(fact)
		}
	}

	return glob.NewEmptyGlobUnknown()
}

func (env *Env) builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(fact *ast.SpecFactStmt) glob.GlobRet {
	// x != 0 store spec Mem
	notEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret := env.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// x >= 0
	greaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(greaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// not x <= 0
	lessEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(lessEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// -x: -1 * x
	minusX := ast.NegateObj(fact.Params[0])

	// x > -x
	greaterThanMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	ret = env.storeSpecFactInMem(greaterThanMinusXFact)
	if ret.IsErr() {
		return ret
	}

	// -x < 0
	minusXLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{minusX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(minusXLessThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// 1/x > 0
	oneDivX := ast.NewFnObj(ast.Atom(glob.KeySymbolSlash), []ast.Obj{ast.Atom("1"), fact.Params[0]})
	oneDivXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{oneDivX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(oneDivXGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// x^2 > 0
	xSquared := ast.NewFnObj(ast.Atom(glob.KeySymbolPower), []ast.Obj{fact.Params[0], ast.Atom("2")})
	xSquaredGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{xSquared, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(xSquaredGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// sqrt(x) > 0
	sqrtX := ast.NewFnObj(ast.Atom("sqrt"), []ast.Obj{fact.Params[0]})
	sqrtXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{sqrtX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(sqrtXGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

func (env *Env) builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsZero(fact *ast.SpecFactStmt) glob.GlobRet {
	// abs(x) = x
	absX := ast.NewFnObj(ast.Atom("abs"), []ast.Obj{fact.Params[0]})
	absXEqualXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{absX, fact.Params[0]}, fact.Line)
	ret := env.storeSpecFactInMem(absXEqualXFact)
	if ret.IsErr() {
		return ret
	}

	// -x: -1 * x
	minusX := ast.NewFnObj(ast.Atom(glob.KeySymbolStar), []ast.Obj{ast.Atom("-1"), fact.Params[0]})

	// x >= -x
	greaterEqualMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	ret = env.storeSpecFactInMem(greaterEqualMinusXFact)
	if ret.IsErr() {
		return ret
	}

	// sqrt(x) >= 0
	sqrtX := ast.NewFnObj(ast.Atom("sqrt"), []ast.Obj{fact.Params[0]})
	sqrtXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{sqrtX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(sqrtXGreaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

func (env *Env) builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(fact *ast.SpecFactStmt) glob.GlobRet {
	// x != 0 store spec Mem
	notEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret := env.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// x <= 0
	lessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(lessEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// not x >= 0
	greaterEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(greaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// -x: -1 * x
	minusX := ast.NewFnObj(ast.Atom(glob.KeySymbolStar), []ast.Obj{ast.Atom("-1"), fact.Params[0]})

	// x < -x
	lessThanMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	ret = env.storeSpecFactInMem(lessThanMinusXFact)
	if ret.IsErr() {
		return ret
	}

	// -x > 0
	minusXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{minusX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(minusXGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// 1/x < 0
	oneDivX := ast.NewFnObj(ast.Atom(glob.KeySymbolSlash), []ast.Obj{ast.Atom("1"), fact.Params[0]})
	oneDivXLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{oneDivX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(oneDivXLessThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// x^2 > 0
	xSquared := ast.NewFnObj(ast.Atom(glob.KeySymbolPower), []ast.Obj{fact.Params[0], ast.Atom("2")})
	xSquaredGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{xSquared, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(xSquaredGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()

}

func (env *Env) builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsZero(fact *ast.SpecFactStmt) glob.GlobRet {
	// abs(x) = -x
	absX := ast.NewFnObj(ast.Atom("abs"), []ast.Obj{fact.Params[0]})
	minusX := ast.NegateObj(fact.Params[0])
	absXEqualMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{absX, minusX}, fact.Line)
	ret := env.storeSpecFactInMem(absXEqualMinusXFact)
	if ret.IsErr() {
		return ret
	}

	// x <= -x
	lessEqualMinusXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], minusX}, fact.Line)
	ret = env.storeSpecFactInMem(lessEqualMinusXFact)
	if ret.IsErr() {
		return ret
	}

	// -x >= 0
	minusXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{minusX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(minusXGreaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

func (env *Env) builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsNotZero(fact *ast.SpecFactStmt) glob.GlobRet {
	// x > c (c != 0)
	// x != c
	notEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := env.storeSpecFactInMem(notEqualCFact)
	if ret.IsErr() {
		return ret
	}

	// x >= c
	greaterEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret = env.storeSpecFactInMem(greaterEqualCFact)
	if ret.IsErr() {
		return ret
	}

	// not x <= c
	lessEqualCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret = env.storeSpecFactInMem(lessEqualCFact)
	if ret.IsErr() {
		return ret
	}

	// c < x (等价表述)
	cLessThanXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = env.storeSpecFactInMem(cLessThanXFact)
	if ret.IsErr() {
		return ret
	}

	// not c >= x
	cGreaterEqualXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = env.storeSpecFactInMem(cGreaterEqualXFact)
	if ret.IsErr() {
		return ret
	}

	// x - c > 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(xMinusCGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// x - c >= 0
	xMinusCGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(xMinusCGreaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// c - x < 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(cMinusXLessThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// c - x <= 0
	cMinusXLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(cMinusXLessEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

func (env *Env) builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsNotZero(fact *ast.SpecFactStmt) glob.GlobRet {
	// x >= c (c != 0)
	// not x < c
	lessCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := env.storeSpecFactInMem(lessCFact)
	if ret.IsErr() {
		return ret
	}

	// c <= x (等价表述)
	cLessEqualXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = env.storeSpecFactInMem(cLessEqualXFact)
	if ret.IsErr() {
		return ret
	}

	// not c > x
	cGreaterXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = env.storeSpecFactInMem(cGreaterXFact)
	if ret.IsErr() {
		return ret
	}

	// x - c >= 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(xMinusCGreaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// c - x <= 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(cMinusXLessEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

func (env *Env) builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsNotZero(fact *ast.SpecFactStmt) glob.GlobRet {
	// x < c (c != 0)
	// x != c
	notEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := env.storeSpecFactInMem(notEqualCFact)
	if ret.IsErr() {
		return ret
	}

	// x <= c
	lessEqualCFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret = env.storeSpecFactInMem(lessEqualCFact)
	if ret.IsErr() {
		return ret
	}

	// not x >= c
	greaterEqualCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret = env.storeSpecFactInMem(greaterEqualCFact)
	if ret.IsErr() {
		return ret
	}

	// c > x (等价表述)
	cGreaterThanXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = env.storeSpecFactInMem(cGreaterThanXFact)
	if ret.IsErr() {
		return ret
	}

	// not c <= x
	cLessEqualXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = env.storeSpecFactInMem(cLessEqualXFact)
	if ret.IsErr() {
		return ret
	}

	// x - c < 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCLessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(xMinusCLessThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// x - c <= 0
	xMinusCLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(xMinusCLessEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// c - x > 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXGreaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(cMinusXGreaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// c - x >= 0
	cMinusXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(cMinusXGreaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

func (env *Env) builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(fact *ast.SpecFactStmt) glob.GlobRet {
	// x <= c (c != 0)
	// not x > c
	greaterCFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := env.storeSpecFactInMem(greaterCFact)
	if ret.IsErr() {
		return ret
	}

	// c >= x (等价表述)
	cGreaterEqualXFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = env.storeSpecFactInMem(cGreaterEqualXFact)
	if ret.IsErr() {
		return ret
	}

	// not c < x
	cLessXFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{fact.Params[1], fact.Params[0]}, fact.Line)
	ret = env.storeSpecFactInMem(cLessXFact)
	if ret.IsErr() {
		return ret
	}

	// x - c <= 0
	xMinusC := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[0], fact.Params[1]})
	xMinusCLessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{xMinusC, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(xMinusCLessEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// c - x >= 0
	cMinusX := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{fact.Params[1], fact.Params[0]})
	cMinusXGreaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{cMinusX, ast.Atom("0")}, fact.Line)
	ret = env.storeSpecFactInMem(cMinusXGreaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}
