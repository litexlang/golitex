// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) btPropExceptEqual_Rule_MemSpec(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !stmt.IsBuiltinProp_ExceptEqual() {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	if ok, err := ver.btInProp(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ast.IsFcAtom_HasGivenName_EmptyPkgName(&stmt.PropName, glob.KeywordCommutativeProp) {
		if ok, err := ver.btCommutativeRule(stmt, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}
	}

	// TODO 处理其他的builtin logic infix opt
	ok, err := ver.btNumberLogicRelaOptBtRule(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.specFactUsingMemSpecifically(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) btNumberLogicRelaOptBtRule(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.PropName.PkgName != "" {
		return false, nil
	}

	if ok, err := ver.btNumberInfixCompareProp(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) btNumberInfixCompareProp(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !glob.IsBuiltinNumberInfixRelaProp(stmt.PropName.Name) {
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

	ok, err = glob.NumLitExprCompareOpt(leftNumLitExpr, rightNumLitExpr, stmt.PropName.Name)

	if err != nil {
		return false, err
	}
	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "builtin rules")
		} else {
			ver.successNoMsg()
		}
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) btCommutativeRule(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !ast.IsFcAtom_HasGivenName_EmptyPkgName(&stmt.PropName, glob.KeywordCommutativeProp) {
		return false, nil
	}

	propNameAsAtom, ok := stmt.Params[0].(*ast.FcAtom)
	if !ok {
		return false, nil
	}

	if ast.IsFcAtom_HasGivenName_EmptyPkgName(propNameAsAtom, glob.KeySymbolEqual) {
		return true, nil
	}

	propDef, ok := ver.env.GetPropDef(*propNameAsAtom)
	if !ok {
		return false, nil
	}

	if len(propDef.DefHeader.Params) != 2 {
		return false, nil
	}

	if ver.env.IsCommutativeProp(stmt.PropName) {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), fmt.Sprintf("prop %s is commutative", stmt.PropName.String()))
		} else {
			ver.successNoMsg()
		}
		return true, nil
	}

	uniFactParams := propDef.DefHeader.Params
	uniFactParamSets := propDef.DefHeader.SetParams
	domFacts := propDef.DomFacts
	ThenFact := propDef.ToSpecFact()
	IffFact, err := ThenFact.ReverseParameterOrder()
	if err != nil {
		return false, err
	}

	uniFact := ast.NewUniFactStmtWithSetReqInDom(uniFactParams, uniFactParamSets, domFacts, []ast.FactStmt{ThenFact}, []ast.FactStmt{IffFact})

	ok, err = ver.FactStmt(uniFact, state.toNoMsg())
	if err != nil {
		return false, err
	}
	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), fmt.Sprintf("the definition of commutative property: %s is true iff\n%s", stmt.String(), uniFact.String()))
		} else {
			ver.successNoMsg()
		}
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) btInProp(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.btLitNumInNatOrIntOrRatOrReal(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// If something is a fn, then it's in fn
	ok, err = ver.btFnInFnSet(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.btPropInPropSet(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) btLitNumInNatOrIntOrRatOrReal(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	isSuccess := false
	defer func() {
		if isSuccess {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), "builtin rules")
			} else {
				ver.successNoMsg()
			}
		}
	}()

	if !stmt.PropName.HasGivenNameAndEmptyPkgName(glob.KeywordIn) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	leftFc, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return false, err
	}
	if ok {
		if ast.IsFcAtom_HasGivenName_EmptyPkgName(stmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtom_HasGivenName_EmptyPkgName(stmt.Params[1], glob.KeywordInt) {
			isSuccess = glob.IsIntegerNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtom_HasGivenName_EmptyPkgName(stmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtom_HasGivenName_EmptyPkgName(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtom_HasGivenName_EmptyPkgName(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftFc)
			return isSuccess, nil
		}
	}

	return false, nil
}

func (ver *Verifier) btFnInFnSet(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !stmt.PropName.HasGivenNameAndEmptyPkgName(glob.KeywordIn) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	asAtom, ok := stmt.Params[0].(*ast.FcAtom)
	if !ok {
		return false, nil
	}

	curEnv := ver.env
	for curEnv != nil {
		_, got := curEnv.FnMem.Get(*asAtom)
		if got {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is a defined %s", asAtom.String(), glob.KeywordFn))
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
		curEnv = curEnv.Parent
	}

	return false, nil
}

func (ver *Verifier) btPropInPropSet(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !stmt.PropName.HasGivenNameAndEmptyPkgName(glob.KeywordIn) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	asAtom, ok := stmt.Params[0].(*ast.FcAtom)
	if !ok {
		return false, nil
	}

	curEnv := ver.env
	for curEnv != nil {
		_, got := curEnv.PropMem.Get(*asAtom)
		if got {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is a defined %s", asAtom.String(), glob.KeywordProp))
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
		curEnv = curEnv.Parent
	}

	return false, nil
}
