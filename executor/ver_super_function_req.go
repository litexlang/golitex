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

func (ver *Verifier) isBuiltinFunction_VerReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
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
		return ver.verCountReq(fnObj, state)
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
	case glob.KeywordChoice:
		return ver.verChoiceReq(fnObj, state)
	case glob.KeywordVal:
		return ver.verValReq(fnObj, state)
	case glob.KeySymbolPlus:
		return ver.verPlusReq(fnObj, state)
	case glob.KeySymbolMinus:
		return ver.verMinusReq(fnObj, state)
	case glob.KeySymbolStar:
		return ver.verStarReq(fnObj, state)
	case glob.KeySymbolSlash:
		return ver.verSlashReq(fnObj, state)
	case glob.KeySymbolPower:
		return ver.verPowerReq(fnObj, state)
	case glob.KeySymbolPercent:
		return ver.verPercentReq(fnObj, state)
	case glob.KeywordRange:
		return ver.verRangeReq(fnObj, state)
	case glob.KeywordClosedRange:
		return ver.verClosedRangeReq(fnObj, state)
	default:
		return ast.NewEmptyUnknownVerRet()
	}
}

func (ver *Verifier) verUnionReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("union expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verIntersectReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("intersect expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verPowerSetReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 1 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("power_set expects 1 parameter, got %d", len(fnObj.Params)))
	}

	_ = state

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verCupReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 1 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("cup expects 1 parameter, got %d", len(fnObj.Params)))
	}

	_ = state

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verCapReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 1 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("cap expects 1 parameter, got %d", len(fnObj.Params)))
	}

	_ = state

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verSetMinusReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("set_minus expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verCountReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 1 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("count expects 1 parameter, got %d", len(fnObj.Params)))
	}

	verRet := ver.VerFactStmt(ast.NewIsAFiniteSetFact(fnObj.Params[0], glob.BuiltinLine0), state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("count parameter must be a finite set, %s in %s is not valid", fnObj.Params[0], fnObj))
	}
	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verSetDiffReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("set_diff expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verProjReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("parameters in %s must be 2, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	// x is cart
	isCartFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIsCart), []ast.Obj{fnObj.Params[0]}, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isCartFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return ast.NewErrVerRet(isCartFact).AddExtraInfo(fmt.Sprintf("%s is unknown", isCartFact))
	}

	// index >= 1
	verRet = ver.VerFactStmt(ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordNPos)), state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("index in %s must be N_pos, %s in %s is not valid", fnObj, fnObj.Params[1], fnObj))
	}

	// index <= set_dim(x)
	verRet = ver.VerFactStmt(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fnObj.Params[1], ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{fnObj.Params[0]})}, glob.BuiltinLine0), state)
	if verRet.IsErr() {
		return verRet
	} else if verRet.IsUnknown() {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("index in %s must be <= set_dim(%s), %s in %s is not valid", fnObj, fnObj.Params[0], fnObj.Params[1], fnObj))
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verDimReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 1 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("parameters in %s must be 1, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}
	// 检查是否是 tuple
	isTupleFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIsTuple), []ast.Obj{fnObj.Params[0]}, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isTupleFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return ast.NewErrVerRet(isTupleFact).AddExtraInfo(fmt.Sprintf("%s is unknown", isTupleFact))
	}
	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verChoiceReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("choice expects 2 parameters, got %d", len(fnObj.Params)))
	}

	// choice(S, s) requires:
	// 1. s $in S (second parameter is in the first parameter)
	// 2. S is a set of non-empty sets: forall x S: $is_nonempty_set(x)
	S := fnObj.Params[0]
	s := fnObj.Params[1]

	// Verify: s $in S
	inFact := ast.NewInFactWithObj(s, S)
	verRet := ver.VerFactStmt(inFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("choice requires that %s is in %s, but this cannot be verified", s, S))
	}

	// Verify: forall x S: $is_nonempty_set(x)
	x := "x"
	uniFact := ast.NewUniFact(
		[]string{x},
		[]ast.Obj{S},
		[]ast.Spec_OrFact{}, // no domain facts
		[]ast.Spec_OrFact{ast.NewIsANonEmptySetFact(ast.Atom(x), glob.BuiltinLine0)},
		glob.BuiltinLine0,
	)

	// Verify the forall statement
	verRet = ver.verUniFact(uniFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("choice requires that all elements of %s are non-empty sets, but this cannot be verified", S))
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verValReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 1 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("val expects 1 parameter, got %d", len(fnObj.Params)))
	}

	return ver.objSatisfyFnReq(fnObj.Params[0], state)
}

func (ver *Verifier) verPlusReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("plus expects 2 parameters, got %d", len(fnObj.Params)))
	}

	// in R
	inRFact := ast.NewInFactWithObj(fnObj.Params[0], ast.Atom(glob.KeywordReal))
	verRet := ver.VerFactStmt(inRFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// in R
	inRFact = ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordReal))
	verRet = ver.VerFactStmt(inRFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}
	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verMinusReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("minus expects 2 parameters, got %d", len(fnObj.Params)))
	}

	// in R
	inRFact := ast.NewInFactWithObj(fnObj.Params[0], ast.Atom(glob.KeywordReal))
	verRet := ver.VerFactStmt(inRFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// in R
	inRFact = ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordReal))
	verRet = ver.VerFactStmt(inRFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verStarReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("star expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	// in R
	inRFact := ast.NewInFactWithObj(fnObj.Params[0], ast.Atom(glob.KeywordReal))
	verRet := ver.VerFactStmt(inRFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// in R
	inRFact = ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordReal))
	verRet = ver.VerFactStmt(inRFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verSlashReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("slash expects 2 parameters, got %d", len(fnObj.Params)))
	}

	// in R
	inRNot0Fact := ast.NewInFactWithObj(fnObj.Params[0], ast.Atom(glob.KeywordReal))
	verRet := ver.VerFactStmt(inRNot0Fact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// in R
	inRNot0Fact = ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordReal))
	verRet = ver.VerFactStmt(inRNot0Fact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// param 1 not zero
	notZeroFact := ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fnObj.Params[1], ast.Atom("0")}, glob.BuiltinLine0)
	verRet = ver.VerFactStmt(notZeroFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verPowerReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("power expects 2 parameters, got %d", len(fnObj.Params)))
	}

	// in R
	inRFact := ast.NewInFactWithObj(fnObj.Params[0], ast.Atom(glob.KeywordReal))
	verRet := ver.VerFactStmt(inRFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// in Z
	inZFact := ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordInteger))
	verRet = ver.VerFactStmt(inZFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// param0 不是 0 or param1 不是 0
	orNotZero := ast.NewOrStmt([]ast.SpecificFactStmt{ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fnObj.Params[0], ast.Atom("0")}, glob.BuiltinLine0), ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fnObj.Params[1], ast.Atom("0")}, glob.BuiltinLine0)}, glob.BuiltinLine0)

	verRet = ver.VerFactStmt(orNotZero, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verPercentReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("percent expects 2 parameters, got %d", len(fnObj.Params)))
	}

	// in Z
	inZFact := ast.NewInFactWithObj(fnObj.Params[0], ast.Atom(glob.KeywordInteger))
	verRet := ver.VerFactStmt(inZFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// in Z
	inZFact = ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordInteger))
	verRet = ver.VerFactStmt(inZFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// y != 0
	notZeroFact := ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fnObj.Params[1], ast.Atom("0")}, glob.BuiltinLine0)
	verRet = ver.VerFactStmt(notZeroFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verRangeReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("range expects 2 parameters, got %d", len(fnObj.Params)))
	}

	// in Z
	inZFact := ast.NewInFactWithObj(fnObj.Params[0], ast.Atom(glob.KeywordInteger))
	verRet := ver.VerFactStmt(inZFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// in Z
	inZFact = ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordInteger))
	verRet = ver.VerFactStmt(inZFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) verClosedRangeReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	if len(fnObj.Params) != 2 {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("closed_range expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	// in Z
	inZFact := ast.NewInFactWithObj(fnObj.Params[0], ast.Atom(glob.KeywordInteger))
	verRet := ver.VerFactStmt(inZFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// in Z
	inZFact = ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordInteger))
	verRet = ver.VerFactStmt(inZFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ast.NewTrueVerRet(nil, nil, "")
}
