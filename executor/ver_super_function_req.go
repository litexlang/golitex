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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) isBuiltinFunction_VerReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	switch fnObj.FnHead.String() {
	case glob.KeywordUnion:
		return ver.verUnionReq(fnObj, state)
	case glob.KeywordIntersect:
		return ver.verIntersectReq(fnObj, state)
	case glob.KeywordPowerSet:
		return ver.verPowerSetReq(fnObj, state)
	case glob.KeywordCup:
		return ver.verCupReq(fnObj, state)
	case glob.KeywordCap:
		return ver.verCapReq(fnObj, state)
	case glob.KeywordSetMinus:
		return ver.verSetMinusReq(fnObj, state)
	case glob.KeywordSetDiff:
		return ver.verSetDiffReq(fnObj, state)
	case glob.KeywordProj:
		return ver.verProjReq(fnObj, state)
	case glob.KeywordDim:
		return ver.verDimReq(fnObj, state)
	case glob.KeywordCount:
		return ver.countFnRequirement(fnObj, state)
	case glob.KeywordCart:
		return ver.cartFnRequirement(fnObj, state)
	case glob.KeywordSetDim:
		return ver.setDimFnRequirement(fnObj, state)
	case glob.KeywordListSet:
		return ver.listSetFnRequirement(fnObj, state)
	case glob.KeywordSetBuilder:
		return ver.SetBuilderFnRequirement(fnObj, state)
	case glob.KeywordTuple:
		return ver.tupleFnReq(fnObj, state)
	case glob.KeywordObjAtIndexOpt:
		return ver.indexOptFnRequirement(fnObj, state)

	default:
		return glob.NewEmptyVerRetUnknown()
	}
}

func (ver *Verifier) verUnionReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), glob.BuiltinLine0, []string{fmt.Sprintf("union expects 2 parameters, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verIntersectReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), glob.BuiltinLine0, []string{fmt.Sprintf("intersect expects 2 parameters, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verPowerSetReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 1 {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), glob.BuiltinLine0, []string{fmt.Sprintf("power_set expects 1 parameter, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verCupReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 1 {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), glob.BuiltinLine0, []string{fmt.Sprintf("cup expects 1 parameter, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verCapReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 1 {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), glob.BuiltinLine0, []string{fmt.Sprintf("cap expects 1 parameter, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verSetMinusReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), glob.BuiltinLine0, []string{fmt.Sprintf("set_minus expects 2 parameters, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verSetDiffReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), glob.BuiltinLine0, []string{fmt.Sprintf("set_diff expects 2 parameters, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verProjReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("parameters in %s must be 2, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj)})
	}

	// x is cart
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fnObj.Params[0]}, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isCartFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return glob.NewVerMsg2(glob.StmtRetTypeError, isCartFact.String(), isCartFact.GetLine(), []string{fmt.Sprintf("%s is unknown", isCartFact)})
	}

	// index >= 1
	verRet = ver.VerFactStmt(ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordNPos)), state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("index in %s must be N_pos, %s in %s is not valid", fnObj, fnObj.Params[1], fnObj)})
	}

	// index <= set_dim(x)
	verRet = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fnObj.Params[1], ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{fnObj.Params[0]})}, glob.BuiltinLine0), state)
	if verRet.IsErr() {
		return verRet
	} else if verRet.IsUnknown() {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("index in %s must be <= set_dim(%s), %s in %s is not valid", fnObj, fnObj.Params[0], fnObj.Params[1], fnObj)})
	}

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verDimReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 1 {
		return glob.NewVerMsg2(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("parameters in %s must be 1, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj)})
	}
	// 检查是否是 tuple
	isTupleFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{fnObj.Params[0]}, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isTupleFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return glob.NewVerMsg2(glob.StmtRetTypeError, isTupleFact.String(), isTupleFact.GetLine(), []string{fmt.Sprintf("%s is unknown", isTupleFact)})
	}
	return glob.NewEmptyVerRetTrue()
}
