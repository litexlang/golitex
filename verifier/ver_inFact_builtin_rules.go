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
// Litex Zulip community: https://litex.zulipchat.com

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

	fnDef, ok := ver.env.GetFnDef(fcFn.FnHead)
	if !ok {
		return false // 这里不传error是有点道理的，因为+-*/的定义不在mem里
	}

	uniMap := map[string]ast.Fc{}
	if len(fnDef.DefHeader.Params) != len(fcFn.ParamSegs) {
		return false
	}

	for i, param := range fnDef.DefHeader.Params {
		uniMap[param] = fcFn.ParamSegs[i]
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
