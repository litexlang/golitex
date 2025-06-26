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

	ok, err := ver.verInSet(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.btLitNumInNatOrIntOrRatOrRealOrComplex(stmt, state)
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
	ok := ast.IsFcAtomEqualToGivenString(stmt.Params[1], glob.KeywordReal)
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

	fnDef, ok := ver.env.GetLatestFnTemplate(fcFn.FnHead)
	if !ok {
		return false // 这里不传error是有点道理的，因为+-*/的定义不在mem里
	}

	uniMap := map[string]ast.Fc{}
	if len(fnDef.Params) != len(fcFn.Params) {
		return false
	}

	for i, param := range fnDef.Params {
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
	ok := ast.IsFcAtomEqualToGivenString(stmt.Params[1], glob.KeywordSet)
	if !ok {
		return false
	}

	asAtom, ok := stmt.Params[0].(ast.FcAtom)
	if !ok {
		return false
	}

	// if asAtom.PkgName != glob.EmptyPkg {
	// 	return false
	// }

	if string(asAtom) == glob.KeywordNatural || string(asAtom) == glob.KeywordInt || string(asAtom) == glob.KeywordReal || string(asAtom) == glob.KeywordComplex || string(asAtom) == glob.KeywordRational {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "the builtin rules")
		} else {
			ver.successNoMsg()
		}
		return true
	}

	return false
}

func (ver *Verifier) verIn_N_Z_Q_R_C_BySpecMem(stmt *ast.SpecFactStmt, state VerState) bool {
	inSet, ok := stmt.Params[1].(ast.FcAtom)
	if !ok {
		return false
	}

	nextState := state.toFinalRound().toNoMsg()

	// if inSet.PkgName != glob.EmptyPkg {
	// 	return false
	// }

	var msg string

	switch string(inSet) {
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
		newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.FcAtom(glob.KeywordNatural)})
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
		newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.FcAtom(glob.KeywordInt)})
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
		newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.FcAtom(glob.KeywordRational)})
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
		newStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[0], ast.FcAtom(glob.KeywordReal)})
		return ver.verInR_BySpecMem(newStmt, state)
	}
	return true, stmt.String()
}

func (ver *Verifier) inFnTemplateFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	var fnTemplate *ast.FnTemplateStmt
	var err error

	if templateName, ok := stmt.Params[1].(ast.FcAtom); ok {
		if !ok {
			return false, nil
		}

		fnTDef, ok := ver.env.GetFnTemplateDef(templateName)
		if !ok {
			return false, nil
		}
		fnTemplate = &fnTDef.FnTemplateStmt
	} else if ast.IsFnFcFn(stmt.Params[1]) {
		fnTemplate, err = ast.FnFcToFnTemplateStmt(stmt.Params[1])
		if err != nil {
			return false, err
		}
	} else {
		return false, nil
	}

	instantiatedDefFnStmt, err := fnTemplate.InstantiateByFnName_WithTemplateNameGivenFc(stmt.Params[0])
	if err != nil {
		return false, nil
	}

	specFactDefs, ok := ver.env.GetFnTemplateOfFc(stmt.Params[0])
	if !ok {
		return false, nil
	}

	for i := len(specFactDefs) - 1; i >= 0; i-- {
		ok, err := ver.leftDomLeadToRightDom_RightDomLeadsToRightThen(stmt.Params[0], specFactDefs[i], instantiatedDefFnStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verInSet(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok := ast.IsFcAtomWithBuiltinPkgAndName(stmt.Params[1], glob.KeywordSet)
	if !ok {
		return false, nil
	}

	// 如果它是N, Z, Q, R, C, 则直接返回true
	ok = ast.IsFcAtomWithBuiltinPkgAndName(stmt.Params[0], glob.KeywordNatural) ||
		ast.IsFcAtomWithBuiltinPkgAndName(stmt.Params[0], glob.KeywordInt) ||
		ast.IsFcAtomWithBuiltinPkgAndName(stmt.Params[0], glob.KeywordRational) ||
		ast.IsFcAtomWithBuiltinPkgAndName(stmt.Params[0], glob.KeywordReal) ||
		ast.IsFcAtomWithBuiltinPkgAndName(stmt.Params[0], glob.KeywordComplex)
	if ok {
		return ver.processOkMsg(state, stmt.String(), "%s is a builtin set", stmt.Params[0].String())
	}

	// 如果是被定义好了的fn_template，则直接返回true
	ok = ast.IsFnFcFn(stmt.Params[1])
	if ok {
		return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", stmt.Params[0].String())
	}

	if leftAsAtom, ok := stmt.Params[0].(ast.FcAtom); ok {
		_, ok := ver.env.GetFnTemplateDef(leftAsAtom)
		if ok {
			return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", leftAsAtom)
		}
	}

	return false, nil
}
