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
func (ver *Verifier) verInFactByRightParamIsNOrZOrQOrR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(stmt ast.SpecificFactStmt, state *VerState) *glob.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	inSet, ok := asPureStmt.Params[1].(ast.Atom)
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
	case glob.KeywordRPos:
		success, verifiedBy = ver.verInRPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordRNeg:
		success, verifiedBy = ver.verInRNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordRNot0:
		success, verifiedBy = ver.verInRNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordZNeg:
		success, verifiedBy = ver.verInZNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordZNot0:
		success, verifiedBy = ver.verInZNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordQPos:
		success, verifiedBy = ver.verInQPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordQNeg:
		success, verifiedBy = ver.verInQNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	case glob.KeywordQNot0:
		success, verifiedBy = ver.verInQNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt, nextState)
	default:
		success = false
	}

	if success {
		if verifiedBy == "" {
			verifiedBy = fmt.Sprintf("%s is in %s", asPureStmt.Params[0], inSet)
		}
		return ver.maybeAddSuccessMsgString(state, stmt.String(), verifiedBy, glob.NewEmptyVerRetTrue())
	}
	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	if ast.IsObjLiterallyNPosNumber(asPureStmt.Params[0]) {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolPlus || fnHead == glob.KeySymbolStar || fnHead == glob.KeySymbolPower {
			ok, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordNPos)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordNPos)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in +*^, and both params are in N_pos", fnObj)
				}
			}
		}
	}

	return false, ""
}

func (ver *Verifier) verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	if ast.IsObjLiterallyNatNumber(asPureStmt.Params[0]) {
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
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolPlus || fnHead == glob.KeySymbolStar || fnHead == glob.KeySymbolPower {
			ok, _ = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordNatural)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordNatural)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in +*^, and both params are in N", fnObj)
				}
			}
		}
	}

	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordNPos)}, glob.BuiltinLine0)
	return ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	if _, ok := ast.IsObjLiterallyIntNumber(asPureStmt.Params[0]); ok {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	if ast.IsFn_WithHeadNameInSlice(asPureStmt.Params[0], glob.AddMinusStarSet) {
		fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordInteger)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordInteger)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in Z", fnObj)
				}
			}
		}
	}

	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordNatural)}, glob.BuiltinLine0)
	return ver.verInN_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	if ast.IsObjLiterallyRationalNumber(asPureStmt.Params[0]) {
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

	if ast.IsFn_WithHeadNameInSlice(asPureStmt.Params[0], glob.AddMinusStarSet) {
		fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordRational)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordRational)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in Q", fnObj)
				}
			}
		}
	}

	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordInteger)}, glob.BuiltinLine0)
	return ver.verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	if ast.IsFn_WithHeadNameInSlice(asPureStmt.Params[0], glob.AddMinusStarSet) {
		fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
		if ok {
			ok, _ = ver.verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordReal)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordReal)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in *+-, and both params are in R", fnObj)
				}
			}
		}
	}

	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordRational)}, glob.BuiltinLine0)
	return ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInRPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	// Check if it's a positive literal number
	if ast.IsObjLiterallyRationalNumber(asPureStmt.Params[0]) {
		atom, ok := asPureStmt.Params[0].(ast.Atom)
		if ok && len(string(atom)) > 0 && string(atom)[0] != '-' {
			return true, stmt.String()
		}
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	// For R_pos, only +, *, ^ preserve R_pos when both operands are in R_pos
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolPlus || fnHead == glob.KeySymbolStar || fnHead == glob.KeySymbolPower {
			ok, _ = ver.verInRPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordRPos)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInRPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordRPos)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in +*^, and both params are in R_pos", fnObj)
				}
			}
		}
	}

	// Try to derive from R
	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordReal)}, glob.BuiltinLine0)
	return ver.verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(newStmt, state)
}

func (ver *Verifier) verInRNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	// Check if it's a negative literal number
	if ast.IsObjLiterallyRationalNumber(asPureStmt.Params[0]) {
		atom, ok := asPureStmt.Params[0].(ast.Atom)
		if ok && len(string(atom)) > 0 && string(atom)[0] == '-' {
			return true, stmt.String()
		}
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	// For R_neg, only -, * preserve R_neg when operands are appropriate
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolMinus {
			// -x is in R_neg if x is in R_pos
			ok, _ = ver.verInRPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordRPos)}, glob.BuiltinLine0), state)
			if ok {
				return true, fmt.Sprintf("%s is -x where x is in R_pos", fnObj)
			}
		} else if fnHead == glob.KeySymbolStar {
			// x * y is in R_neg if one is in R_pos and the other is in R_neg
			ok1, _ := ver.verInRPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordRPos)}, glob.BuiltinLine0), state)
			ok2, _ := ver.verInRNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordRNeg)}, glob.BuiltinLine0), state)
			if ok1 && ok2 {
				return true, fmt.Sprintf("%s has * with one param in R_pos and one in R_neg", fnObj)
			}
			ok1, _ = ver.verInRNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordRNeg)}, glob.BuiltinLine0), state)
			ok2, _ = ver.verInRPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordRPos)}, glob.BuiltinLine0), state)
			if ok1 && ok2 {
				return true, fmt.Sprintf("%s has * with one param in R_neg and one in R_pos", fnObj)
			}
		}
	}

	// Try to derive from R
	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordReal)}, glob.BuiltinLine0)
	return ver.verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(newStmt, state)
}

func (ver *Verifier) verInRNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	// Check if it's a non-zero literal number
	if ast.IsObjLiterallyRationalNumber(asPureStmt.Params[0]) {
		atom, ok := asPureStmt.Params[0].(ast.Atom)
		if ok && string(atom) != "0" && string(atom) != "-0" {
			return true, stmt.String()
		}
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	// For R_not0, *, / preserve R_not0 when operands are in R_not0
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolStar || fnHead == glob.KeySymbolSlash {
			ok, _ = ver.verInRNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordRNot0)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInRNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordRNot0)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in */, and both params are in R_not0", fnObj)
				}
			}
		}
	}

	// Try to derive from R
	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordReal)}, glob.BuiltinLine0)
	return ver.verInR_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(newStmt, state)
}

func (ver *Verifier) verInZNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	// Check if it's a negative integer literal
	if val, ok := ast.IsObjLiterallyIntNumber(asPureStmt.Params[0]); ok && val < 0 {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	// For Z_neg, only -, * preserve Z_neg when operands are appropriate
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolMinus {
			// -x is in Z_neg if x is in N_pos
			ok, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordNPos)}, glob.BuiltinLine0), state)
			if ok {
				return true, fmt.Sprintf("%s is -x where x is in N_pos", fnObj)
			}
		} else if fnHead == glob.KeySymbolStar {
			// x * y is in Z_neg if one is in N_pos and the other is in Z_neg
			ok1, _ := ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordNPos)}, glob.BuiltinLine0), state)
			ok2, _ := ver.verInZNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordZNeg)}, glob.BuiltinLine0), state)
			if ok1 && ok2 {
				return true, fmt.Sprintf("%s has * with one param in N_pos and one in Z_neg", fnObj)
			}
			ok1, _ = ver.verInZNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordZNeg)}, glob.BuiltinLine0), state)
			ok2, _ = ver.verInNPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordNPos)}, glob.BuiltinLine0), state)
			if ok1 && ok2 {
				return true, fmt.Sprintf("%s has * with one param in Z_neg and one in N_pos", fnObj)
			}
		}
	}

	// Try to derive from Z
	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordInteger)}, glob.BuiltinLine0)
	return ver.verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInZNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	// Check if it's a non-zero integer literal
	if val, ok := ast.IsObjLiterallyIntNumber(asPureStmt.Params[0]); ok && val != 0 {
		return true, stmt.String()
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	// For Z_not0, *, / preserve Z_not0 when operands are in Z_not0
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolStar || fnHead == glob.KeySymbolSlash {
			ok, _ = ver.verInZNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordZNot0)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInZNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordZNot0)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in */, and both params are in Z_not0", fnObj)
				}
			}
		}
	}

	// Try to derive from Z
	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordInteger)}, glob.BuiltinLine0)
	return ver.verInZ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInQPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	// Check if it's a positive rational literal number
	if ast.IsObjLiterallyRationalNumber(asPureStmt.Params[0]) {
		atom, ok := asPureStmt.Params[0].(ast.Atom)
		if ok && len(string(atom)) > 0 && string(atom)[0] != '-' {
			return true, stmt.String()
		}
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	// For Q_pos, only +, *, / preserve Q_pos when both operands are in Q_pos
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolPlus || fnHead == glob.KeySymbolStar || fnHead == glob.KeySymbolSlash {
			ok, _ = ver.verInQPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordQPos)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInQPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordQPos)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in +*/, and both params are in Q_pos", fnObj)
				}
			}
		}
	}

	// Try to derive from Q
	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordRational)}, glob.BuiltinLine0)
	return ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInQNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	// Check if it's a negative rational literal number
	if ast.IsObjLiterallyRationalNumber(asPureStmt.Params[0]) {
		atom, ok := asPureStmt.Params[0].(ast.Atom)
		if ok && len(string(atom)) > 0 && string(atom)[0] == '-' {
			return true, stmt.String()
		}
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	// For Q_neg, only -, * preserve Q_neg when operands are appropriate
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolMinus {
			// -x is in Q_neg if x is in Q_pos
			ok, _ = ver.verInQPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordQPos)}, glob.BuiltinLine0), state)
			if ok {
				return true, fmt.Sprintf("%s is -x where x is in Q_pos", fnObj)
			}
		} else if fnHead == glob.KeySymbolStar {
			// x * y is in Q_neg if one is in Q_pos and the other is in Q_neg
			ok1, _ := ver.verInQPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordQPos)}, glob.BuiltinLine0), state)
			ok2, _ := ver.verInQNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordQNeg)}, glob.BuiltinLine0), state)
			if ok1 && ok2 {
				return true, fmt.Sprintf("%s has * with one param in Q_pos and one in Q_neg", fnObj)
			}
			ok1, _ = ver.verInQNeg_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordQNeg)}, glob.BuiltinLine0), state)
			ok2, _ = ver.verInQPos_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordQPos)}, glob.BuiltinLine0), state)
			if ok1 && ok2 {
				return true, fmt.Sprintf("%s has * with one param in Q_neg and one in Q_pos", fnObj)
			}
		}
	}

	// Try to derive from Q
	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordRational)}, glob.BuiltinLine0)
	return ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}

func (ver *Verifier) verInQNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(stmt ast.SpecificFactStmt, state *VerState) (bool, string) {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return false, ""
	}

	// Check if it's a non-zero rational literal number
	if ast.IsObjLiterallyRationalNumber(asPureStmt.Params[0]) {
		atom, ok := asPureStmt.Params[0].(ast.Atom)
		if ok && string(atom) != "0" && string(atom) != "-0" {
			return true, stmt.String()
		}
	}

	verRet := ver.verSpecFact_BySpecMem(asPureStmt, state)
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

	// For Q_not0, *, / preserve Q_not0 when operands are in Q_not0
	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if ok {
		fnHead := fnObj.FnHead.String()
		if fnHead == glob.KeySymbolStar || fnHead == glob.KeySymbolSlash {
			ok, _ = ver.verInQNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[0], ast.Atom(glob.KeywordQNot0)}, glob.BuiltinLine0), state)
			if ok {
				ok, _ = ver.verInQNot0_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{fnObj.Params[1], ast.Atom(glob.KeywordQNot0)}, glob.BuiltinLine0), state)
				if ok {
					return true, fmt.Sprintf("%s has function name in */, and both params are in Q_not0", fnObj)
				}
			}
		}
	}

	// Try to derive from Q
	newStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{asPureStmt.Params[0], ast.Atom(glob.KeywordRational)}, glob.BuiltinLine0)
	return ver.verInQ_BySpecMem_ReturnValueOfUserDefinedFnInFnReturnSet(newStmt, state)
}
