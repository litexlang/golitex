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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// 这是必要的，因为 2 $in N 是这个检查的
func (ver *Verifier) verIn_N_Z_Q_R_C(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	inSet, ok := stmt.Params[1].(ast.AtomObj)
	if !ok {
		return NewExecUnknown("")
	}

	nextState := state.GetFinalRound().GetNoMsg()
	var verifiedBy string
	var success bool
	switch string(inSet) {
	case glob.KeywordNatural:
		success, verifiedBy = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordInteger:
		success, verifiedBy = ver.verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordRational:
		success, verifiedBy = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordNPos:
		success, verifiedBy = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordReal:
		success, verifiedBy = ver.verInR_BySpecMem(stmt, nextState)
	case glob.KeywordComplex:
		success, verifiedBy = ver.verInC_BySpecMem(stmt, nextState)
	default:
		success = false
	}

	if success {
		if verifiedBy == "" {
			verifiedBy = fmt.Sprintf("%s is in %s", stmt.Params[0], inSet)
		}
		return ver.maybeAddSuccessMsg(state, stmt.String(), verifiedBy, NewExecTrue(""))
	}
	return NewExecUnknown("")
}

func (ver *Verifier) verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	if ast.IsFcLiterallyNPosNumber(stmt.Params[0]) {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	if ast.IsFn_WithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) || ast.IsFn_WithHeadName(stmt.Params[0], glob.KeySymbolPower) {
		objFn, ok := stmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[0], ast.AtomObj(glob.KeywordNPos)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[1], ast.AtomObj(glob.KeywordNPos)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-^, and both params are in N_pos", objFn)
				}
			}
		}
	}

	return false, ""
}

func (ver *Verifier) verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	if ast.IsFcLiterallyNatNumber(stmt.Params[0]) {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	if ast.IsFn_WithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) || ast.IsFn_WithHeadName(stmt.Params[0], glob.KeySymbolPower) {
		objFn, ok := stmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[0], ast.AtomObj(glob.KeywordNatural)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[1], ast.AtomObj(glob.KeywordNatural)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-^, and both params are in N", objFn)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.AtomObj(glob.KeywordNPos)}, stmt.Line)
	return ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	if ast.IsFcLiterallyIntNumber(stmt.Params[0]) {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	if ast.IsFn_WithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) {
		objFn, ok := stmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[0], ast.AtomObj(glob.KeywordInteger)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[1], ast.AtomObj(glob.KeywordInteger)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in Z", objFn)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.AtomObj(glob.KeywordNatural)}, stmt.Line)
	return ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	if ast.IsFcLiterallyRationalNumber(stmt.Params[0]) {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}

	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	if ast.IsFn_WithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) {
		objFn, ok := stmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[0], ast.AtomObj(glob.KeywordRational)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[1], ast.AtomObj(glob.KeywordRational)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in Q", objFn)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.AtomObj(glob.KeywordInteger)}, stmt.Line)
	return ver.verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInR_BySpecMem(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}

	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	if ast.IsFn_WithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) {
		objFn, ok := stmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInR_BySpecMem(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[0], ast.AtomObj(glob.KeywordReal)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInR_BySpecMem(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{objFn.Params[1], ast.AtomObj(glob.KeywordReal)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in R", objFn)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.AtomObj(glob.KeywordRational)}, stmt.Line)
	return ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInC_BySpecMem(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.AtomObj(glob.KeywordReal)}, stmt.Line)
	return ver.verInR_BySpecMem(newStmt, state)
}
