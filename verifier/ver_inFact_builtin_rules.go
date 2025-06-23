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
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (ver *Verifier) inFactBuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("invalid number of parameters for in fact")
	}

	ok, err := ver.btLitNumInNatOrIntOrRatOrRealOrComplex(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok = ver.builtinSetsInSetSet(stmt, state)
	if ok {
		return true, nil
	}

	ok = ver.returnValueOfBuiltinArithmeticFnInReal(stmt, state)
	if ok {
		return true, nil
	}

	ok = ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if ok {
		return true, nil
	}

	ok = ver.verIn_N_Z_Q_R_C_BySpecMem(stmt, state)
	if ok {
		return true, nil
	}

	ok, err = ver.inFnTemplateFact(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) returnValueOfBuiltinArithmeticFnInReal(stmt *ast.SpecFactStmt, state VerState) bool {
	ok := ast.IsFcAtomWithNameAndEmptyPkg(stmt.Params[1], glob.KeywordReal)
	if !ok {
		return false
	}

	ok = ast.IsFn_WithHeadNameInSlice(stmt.Params[0], []string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower})

	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "the return value of the builtin arithmetic function is in the real set")
		} else {
			ver.successNoMsg()
		}
		return true
	} else {
		return false
	}
}

func (ver *Verifier) returnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state VerState) bool {
	fcFn, ok := stmt.Params[0].(*ast.FcFn)
	if !ok {
		return false
	}

	fnDef, ok := ver.env.GetLatestFnDef(fcFn.FnHead)
	if !ok {
		return false // 这里不传error是有点道理的，因为+-*/的定义不在mem里
	}

	uniMap := map[string]ast.Fc{}
	if len(fnDef.DefHeader.Params) != len(fcFn.Params) {
		return false
	}

	for i, param := range fnDef.DefHeader.Params {
		uniMap[param] = fcFn.Params[i]
	}

	instantiatedRetSet, err := fnDef.RetSet.Instantiate(uniMap)
	if err != nil {
		return false
	}

	ok = cmp.CmpFcAsStr(stmt.Params[1], instantiatedRetSet)
	if !ok {
		return false
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), "the return value of the user defined function is in the function return set")
	} else {
		ver.successNoMsg()
	}

	return true
}

func (ver *Verifier) builtinSetsInSetSet(stmt *ast.SpecFactStmt, state VerState) bool {
	ok := ast.IsFcAtomWithNameAndEmptyPkg(stmt.Params[1], glob.KeywordSet)
	if !ok {
		return false
	}

	asAtom, ok := stmt.Params[0].(*ast.FcAtom)
	if !ok {
		return false
	}

	if asAtom.PkgName != glob.EmptyPkg {
		return false
	}

	if asAtom.Name == glob.KeywordNatural || asAtom.Name == glob.KeywordInt || asAtom.Name == glob.KeywordReal || asAtom.Name == glob.KeywordComplex || asAtom.Name == glob.KeywordRational {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "the builtin rules")
		} else {
			ver.successNoMsg()
		}
		return true
	}

	return false
}

// this might lead to Russell's paradox
// func (ver *Verifier) anythingIsInObj(stmt *ast.SpecFactStmt, state VerState) bool {
// 	ok := ast.IsFcAtomWithNameAndEmptyPkg(stmt.Params[1], glob.KeywordObj)
// 	if ok {
// 		if state.requireMsg() {
// 			ver.successWithMsg(stmt.String(), "anything is in the obj set")
// 		} else {
// 			ver.successNoMsg()
// 		}
// 		return true
// 	}

// 	return false
// }

func (ver *Verifier) verIn_N_Z_Q_R_C_BySpecMem(stmt *ast.SpecFactStmt, state VerState) bool {
	inSet, ok := stmt.Params[1].(*ast.FcAtom)
	if !ok {
		return false
	}

	nextState := state.toFinalRound().toNoMsg()

	if inSet.PkgName != glob.EmptyPkg {
		return false
	}

	var msg string

	switch inSet.Name {
	case glob.KeywordNatural:
		ok, msg = ver.verInN_BySpecMem(stmt, nextState)
	case glob.KeywordInt:
		ok, msg = ver.verInZ_BySpecMem(stmt, nextState)
	case glob.KeywordRational:
		ok, msg = ver.verInQ_BySpecMem(stmt, nextState)
	case glob.KeywordReal:
		ok, msg = ver.verInR_BySpecMem(stmt, nextState)
	case glob.KeywordComplex:
		ok, msg = ver.verInC_BySpecMem(stmt, nextState)
	default:
		ok = false
		msg = ""
	}

	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), msg)
		} else {
			ver.successNoMsg()
		}
		return true
	}
	return false
}

func (ver *Verifier) verInN_BySpecMem(stmt *ast.SpecFactStmt, state VerState) (bool, string) {
	ok, err := ver.verSpecFact_BySpecMem(stmt, state)
	if err != nil {
		return false, ""
	}

	return ok, stmt.String()
}

func (ver *Verifier) verInZ_BySpecMem(stmt *ast.SpecFactStmt, state VerState) (bool, string) {
	ok, err := ver.verSpecFact_BySpecMem(stmt, state)
	if err != nil {
		return false, ""
	}
	if !ok {
		newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.NewFcAtomWithName(glob.KeywordNatural)})
		return ver.verInN_BySpecMem(newStmt, state)
	}
	return true, stmt.String()
}

func (ver *Verifier) verInQ_BySpecMem(stmt *ast.SpecFactStmt, state VerState) (bool, string) {
	ok, err := ver.verSpecFact_BySpecMem(stmt, state)
	if err != nil {
		return false, ""
	}
	if !ok {
		newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.NewFcAtomWithName(glob.KeywordInt)})
		return ver.verInZ_BySpecMem(newStmt, state)
	}
	return true, stmt.String()
}

func (ver *Verifier) verInR_BySpecMem(stmt *ast.SpecFactStmt, state VerState) (bool, string) {
	ok, err := ver.verSpecFact_BySpecMem(stmt, state)
	if err != nil {
		return false, ""
	}
	if !ok {
		newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.NewFcAtomWithName(glob.KeywordRational)})
		return ver.verInQ_BySpecMem(newStmt, state)
	}
	return true, stmt.String()
}

func (ver *Verifier) verInC_BySpecMem(stmt *ast.SpecFactStmt, state VerState) (bool, string) {
	ok, err := ver.verSpecFact_BySpecMem(stmt, state)
	if err != nil {
		return false, ""
	}
	if !ok {
		newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.NewFcAtomWithName(glob.KeywordReal)})
		return ver.verInR_BySpecMem(newStmt, state)
	}
	return true, stmt.String()
}

func (ver *Verifier) inFnTemplateFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	templateName, ok := stmt.Params[1].(*ast.FcAtom)
	if !ok {
		return false, nil
	}

	fnT, ok := ver.env.GetFnTemplateDef(templateName)
	if !ok {
		return false, nil
	}

	instantiatedDefFnStmt, err := fnT.InstantiateByFnName(stmt.Params[0].String())
	if err != nil {
		return false, nil
	}

	specFactDefs, ok := ver.env.GetFnDefs(stmt.Params[0])
	if !ok {
		return false, nil
	}

	for i := len(specFactDefs) - 1; i >= 0; i-- {
		ok, err := ver.leftDomLeadToRightDom_RightDomLeadsToRightThen(specFactDefs[i], instantiatedDefFnStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}

// left dom >= right dom
// left dom + left then + right dom => right then
func (ver *Verifier) leftDomLeadToRightDom_RightDomLeadsToRightThen(leftFnDef *ast.DefFnStmt, rightFnDef *ast.DefFnStmt, state VerState) (bool, error) {
	if len(leftFnDef.DefHeader.Params) != len(rightFnDef.DefHeader.Params) {
		return false, fmt.Errorf("the number of parameters of the left function definition is not equal to the number of parameters of the right function definition")
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range rightFnDef.DefHeader.Params {
		uniMap[param] = ast.NewFcAtomWithName(leftFnDef.DefHeader.Params[i])
	}

	instantiatedSetParamsInFacts, instantiatedDomFacts, instantiatedThenFacts, instantiatedRetSet, err := rightFnDef.Instantiate_SetParamsInFacts_DomFacts_ThenFacts_RetSet(uniMap)
	if err != nil {
		return false, err
	}

	fcFnParams := []ast.Fc{}
	for _, param := range leftFnDef.DefHeader.Params {
		fcFnParams = append(fcFnParams, ast.NewFcAtomWithName(param))
	}
	fcFn := ast.NewFcFn(ast.NewFcAtomWithName(leftFnDef.DefHeader.Name), fcFnParams)

	fcFnInLeftRetSet := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{fcFn, leftFnDef.RetSet})

	// left dom => right dom
	leftDomToRightDomUniFact := ast.NewUniFact(leftFnDef.DefHeader.Params, leftFnDef.DefHeader.SetParams, leftFnDef.DomFacts, append(instantiatedSetParamsInFacts, instantiatedThenFacts...))

	ok, err := ver.VerFactStmt(leftDomToRightDomUniFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	// left dom + left in set params + left then + right dom + right in set params => right then
	leftDomToRightDomFacts := []ast.FactStmt{}
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, leftFnDef.DomFacts...)
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, fcFnInLeftRetSet)
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, leftFnDef.ThenFacts...)
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, instantiatedSetParamsInFacts...)
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, instantiatedDomFacts...)

	rightThenFacts := []ast.FactStmt{}
	rightThenFacts = append(rightThenFacts, ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{fcFn, instantiatedRetSet}))
	rightThenFacts = append(rightThenFacts, instantiatedThenFacts...)

	leftDom_leftThen_rightDom_rightThen_uniFact := ast.NewUniFact(leftFnDef.DefHeader.Params, leftFnDef.DefHeader.SetParams, leftDomToRightDomFacts, rightThenFacts)

	if ok, err := ver.VerFactStmt(leftDom_leftThen_rightDom_rightThen_uniFact, state); err != nil || !ok {
		return false, err
	}

	return true, nil
}
