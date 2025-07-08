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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verNumberLogicRelaOpt_BuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// if stmt.PropName.PkgName != "" {
	// 	return false, nil
	// }

	if ok, err := ver.btNumberInfixCompareProp(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) btNumberInfixCompareProp(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !glob.IsBuiltinNumberInfixRelaProp(string(stmt.PropName)) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	leftNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[1])
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = glob.NumLitExprCompareOpt(leftNumLitExpr, rightNumLitExpr, string(stmt.PropName))

	if err != nil {
		return false, err
	}
	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "builtin rules")
		}
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) varCommutativeProp_BuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.PropName != glob.KeywordCommutativeProp {
		return false, nil
	}

	propNameAsAtom, ok := stmt.Params[0].(ast.FcAtom)
	if !ok {
		return false, nil
	}

	// if ast.IsFcAtomEqualToGivenString(propNameAsAtom, glob.KeySymbolEqual) {
	if propNameAsAtom == glob.KeySymbolEqual {
		return true, nil
	}

	propDef, ok := ver.env.GetPropDef(propNameAsAtom)
	if !ok {
		return false, nil
	}

	if len(propDef.DefHeader.Params) != 2 {
		return false, nil
	}

	if ver.isCommutativeProp_BuiltinRule(stmt) {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), fmt.Sprintf("prop %v is commutative", stmt.PropName))
		}
		return true, nil
	}

	uniFactParams := propDef.DefHeader.Params
	domFacts := propDef.DomFacts
	ThenFact := propDef.ToSpecFact()
	IffFact, err := ThenFact.ReverseParameterOrder()
	if err != nil {
		return false, err
	}

	uniFact := ast.NewUniFactWithIff(ast.NewUniFact(uniFactParams, propDef.DefHeader.ParamSets, domFacts, []ast.FactStmt{ThenFact}), []ast.FactStmt{IffFact})

	ok, err = ver.VerFactStmt(uniFact, state.toNoMsg())
	if err != nil {
		return false, err
	}
	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), fmt.Sprintf("the definition of commutative property: %v is true iff\n%v", stmt, uniFact))
		}
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) btLitNumInNatOrIntOrRatOrRealOrComplex(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.PropName != glob.KeywordIn {
		return false, nil
	}

	isSuccess := false
	defer func() {
		if isSuccess {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), "builtin rules")
			}
		}
	}()

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	leftFc, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return false, err
	}
	if ok {
		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordInt) {
			isSuccess = glob.IsIntegerNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordComplex) {
			isSuccess = glob.IsComplexNumLitExpr(leftFc)
			return isSuccess, nil
		}
	}

	return false, nil
}
