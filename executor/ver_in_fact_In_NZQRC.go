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

// 这是必要的，因为 2 $in N 是这个检查的
func (ver *Verifier) verInFactByRightParamIsNOrZOrQOrR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	inSet, ok := stmt.Params[1].(ast.Atom)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	nextState := state.GetFinalRound().GetNoMsg()
	var verifiedBy string
	var success bool
	switch string(inSet) {
	case glob.KeywordNatural:
		success, verifiedBy = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordInteger:
		success, verifiedBy = ver.verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordRational:
		success, verifiedBy = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordNPos:
		success, verifiedBy = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordReal:
		success, verifiedBy = ver.verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(stmt, nextState)
	default:
		success = false
	}

	if success {
		if verifiedBy == "" {
			verifiedBy = fmt.Sprintf("%s is in %s", stmt.Params[0], inSet)
		}
		return ver.maybeAddSuccessMsgString(state, stmt.String(), verifiedBy, glob.NewEmptyVerRetTrue())
	}
	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	if ast.IsObjLiterallyNPosNumber(stmt.Params[0]) {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.verInFactByLeftParamIsReturnValueOfUserDefinedFn(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	// For N_pos, only +, *, ^ preserve N_pos when both operands are in N_pos
	// Subtraction (-) does NOT preserve N_pos (e.g., 3 - 5 = -2 is not in N_pos)
	fnObj, ok := stmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolPlus || fnHead == glob.KeySymbolStar || fnHead == glob.KeySymbolPower {
			ok, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordNPos)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordNPos)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in +*^, and both params are in N_pos", fnObj)
				}
			}
		}
	}

	return false, ""
}

func (ver *Verifier) verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	if ast.IsObjLiterallyNatNumber(stmt.Params[0]) {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.verInFactByLeftParamIsReturnValueOfUserDefinedFn(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	// For N (natural numbers including 0), only +, *, ^ preserve N when both operands are in N
	// Subtraction (-) does NOT preserve N (e.g., 1 - 2 = -1 is not in N)
	fnObj, ok := stmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolPlus || fnHead == glob.KeySymbolStar || fnHead == glob.KeySymbolPower {
			ok, _ = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordNatural)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordNatural)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in +*^, and both params are in N", fnObj)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.Atom(glob.KeywordNPos)}, stmt.Line)
	return ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	if _, ok := ast.IsObjLiterallyIntNumber(stmt.Params[0]); ok {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.verInFactByLeftParamIsReturnValueOfUserDefinedFn(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	if ast.IsFn_WithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) {
		fnObj, ok := stmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordInteger)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordInteger)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in Z", fnObj)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.Atom(glob.KeywordNatural)}, stmt.Line)
	return ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	if ast.IsObjLiterallyRationalNumber(stmt.Params[0]) {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}

	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.verInFactByLeftParamIsReturnValueOfUserDefinedFn(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	if ast.IsFn_WithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) {
		fnObj, ok := stmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordRational)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordRational)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in Q", fnObj)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.Atom(glob.KeywordInteger)}, stmt.Line)
	return ver.verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(stmt *ast.SpecFactStmt, state *VerState) (bool, string) {
	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}

	if verRet.IsTrue() {
		return true, stmt.String()
	}

	verRet = ver.verInFactByLeftParamIsReturnValueOfUserDefinedFn(stmt, state)
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	if ast.IsFn_WithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) {
		fnObj, ok := stmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordReal)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordReal)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in R", fnObj)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.Atom(glob.KeywordRational)}, stmt.Line)
	return ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}
