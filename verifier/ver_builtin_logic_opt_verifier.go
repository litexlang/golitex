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
	if !ast.IsFcAtomWithName(&stmt.PropName, glob.KeywordCommutativeProp) {
		return false, nil
	}

	propNameAsAtom, ok := stmt.Params[0].(*ast.FcAtom)
	if !ok {
		return false, nil
	}

	if ast.IsFcAtomWithName(propNameAsAtom, glob.KeySymbolEqual) {
		return true, nil
	}

	propDef, ok := ver.env.GetPropDef(*propNameAsAtom)
	if !ok {
		return false, nil
	}

	if len(propDef.DefHeader.Params) != 2 {
		return false, nil
	}

	if ver.isCommutativeProp(stmt) {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), fmt.Sprintf("prop %s is commutative", stmt.PropName.String()))
		} else {
			ver.successNoMsg()
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

	uniFact := ast.NewUniFactStmtWithSetReqInDom(uniFactParams, propDef.DefHeader.SetParams, domFacts, []ast.FactStmt{ThenFact}, []ast.FactStmt{IffFact}, propDef.DefHeader.ParamInSetsFacts)

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
		if ast.IsFcAtomWithName(stmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomWithName(stmt.Params[1], glob.KeywordInt) {
			isSuccess = glob.IsIntegerNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomWithName(stmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomWithName(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomWithName(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftFc)
			return isSuccess, nil
		}
	}

	return false, nil
}

// func (ver *Verifier) btFnInFnSet(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	if !stmt.PropName.HasGivenNameAndEmptyPkgName(glob.KeywordIn) {
// 		return false, nil
// 	}

// 	if len(stmt.Params) != 2 {
// 		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
// 	}

// 	asAtom, ok := stmt.Params[0].(*ast.FcAtom)
// 	if !ok {
// 		return false, nil
// 	}

// 	curEnv := ver.env
// 	for curEnv != nil {
// 		_, got := curEnv.FnDefMem.Get(*asAtom)
// 		if got {
// 			if state.requireMsg() {
// 				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is a defined %s", asAtom.String(), glob.KeywordFn))
// 			} else {
// 				ver.successNoMsg()
// 			}
// 			return true, nil
// 		}
// 		curEnv = curEnv.Parent
// 	}

// 	return false, nil
// }

// func (ver *Verifier) btPropInPropSet(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	if !stmt.PropName.HasGivenNameAndEmptyPkgName(glob.KeywordIn) {
// 		return false, nil
// 	}

// 	if len(stmt.Params) != 2 {
// 		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
// 	}

// 	asAtom, ok := stmt.Params[0].(*ast.FcAtom)
// 	if !ok {
// 		return false, nil
// 	}

// 	curEnv := ver.env
// 	for curEnv != nil {
// 		_, got := curEnv.PropDefMem.Get(*asAtom)
// 		if got {
// 			if state.requireMsg() {
// 				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is a defined %s", asAtom.String(), glob.KeywordProp))
// 			} else {
// 				ver.successNoMsg()
// 			}
// 			return true, nil
// 		}
// 		curEnv = curEnv.Parent
// 	}

// 	return false, nil
// }
