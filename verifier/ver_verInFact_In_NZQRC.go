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

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// 这是必要的，因为 2 $in N 是这个检查的
func (ver *Verifier) verIn_N_Z_Q_R_C(stmt *ast.SpecificFactStmt, state *VerState) bool {
	inSet, ok := stmt.Params[1].(ast.FcAtom)
	if !ok {
		return false
	}

	nextState := state.GetFinalRound().GetNoMsg()
	var msg string
	switch string(inSet) {
	case glob.KeywordNatural:
		ok, msg = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordInteger:
		ok, msg = ver.verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordRational:
		ok, msg = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordNPos:
		ok, msg = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordReal:
		ok, msg = ver.verInR_BySpecMem(stmt, nextState)
	case glob.KeywordComplex:
		ok, msg = ver.verInC_BySpecMem(stmt, nextState)
	default:
		ok = false
		msg = ""
	}

	if ok {
		if state.WithMsg {
			ver.successWithMsg(stmt.String(), msg)
		}
		return true
	}
	return false
}

func (ver *Verifier) verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecificFactStmt, state *VerState) (bool, string) {
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

	ok := ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if ok {
		return true, stmt.String()
	}

	if ast.IsFcFnWithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) || ast.IsFcFnWithHeadName(stmt.Params[0], glob.KeySymbolPower) {
		fcFn, ok := stmt.Params[0].(*ast.FcFn)
		if ok {
			ok, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[0], ast.FcAtom(glob.KeywordNPos)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[1], ast.FcAtom(glob.KeywordNPos)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-^, and both params are in N_pos", fcFn)
				}
			}
		}
	}

	return false, ""
}

func (ver *Verifier) verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecificFactStmt, state *VerState) (bool, string) {
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

	ok := ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if ok {
		return true, stmt.String()
	}

	if ast.IsFcFnWithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) || ast.IsFcFnWithHeadName(stmt.Params[0], glob.KeySymbolPower) {
		fcFn, ok := stmt.Params[0].(*ast.FcFn)
		if ok {
			ok, _ = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[0], ast.FcAtom(glob.KeywordNatural)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[1], ast.FcAtom(glob.KeywordNatural)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-^, and both params are in N", fcFn)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.FcAtom(glob.KeywordNPos)}, stmt.Line)
	return ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecificFactStmt, state *VerState) (bool, string) {
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

	ok := ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if ok {
		return true, stmt.String()
	}

	if ast.IsFcFnWithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) {
		fcFn, ok := stmt.Params[0].(*ast.FcFn)
		if ok {
			ok, _ = ver.verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[0], ast.FcAtom(glob.KeywordInteger)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[1], ast.FcAtom(glob.KeywordInteger)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in Z", fcFn)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.FcAtom(glob.KeywordNatural)}, stmt.Line)
	return ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecificFactStmt, state *VerState) (bool, string) {
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

	ok := ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if ok {
		return true, stmt.String()
	}

	if ast.IsFcFnWithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) {
		fcFn, ok := stmt.Params[0].(*ast.FcFn)
		if ok {
			ok, _ = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[0], ast.FcAtom(glob.KeywordRational)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[1], ast.FcAtom(glob.KeywordRational)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in Q", fcFn)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.FcAtom(glob.KeywordInteger)}, stmt.Line)
	return ver.verInZ_BySpecMem__ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInR_BySpecMem(stmt *ast.SpecificFactStmt, state *VerState) (bool, string) {
	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}

	if verRet.IsTrue() {
		return true, stmt.String()
	}

	ok := ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if ok {
		return true, stmt.String()
	}

	if ast.IsFcFnWithHeadNameInSlice(stmt.Params[0], glob.AddMinusStarSet) {
		fcFn, ok := stmt.Params[0].(*ast.FcFn)
		if ok {
			ok, _ = ver.verInR_BySpecMem(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[0], ast.FcAtom(glob.KeywordReal)}, stmt.Line), state)
			if ok {
				ok, _ = ver.verInR_BySpecMem(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fcFn.Params[1], ast.FcAtom(glob.KeywordReal)}, stmt.Line), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in R", fcFn)
				}
			}
		}
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.FcAtom(glob.KeywordRational)}, stmt.Line)
	return ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInC_BySpecMem(stmt *ast.SpecificFactStmt, state *VerState) (bool, string) {
	verRet := ver.verSpecFact_BySpecMem(stmt, state)
	if verRet.IsErr() {
		return false, ""
	}
	if verRet.IsTrue() {
		return true, stmt.String()
	}

	newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.FcAtom(glob.KeywordReal)}, stmt.Line)
	return ver.verInR_BySpecMem(newStmt, state)
}
