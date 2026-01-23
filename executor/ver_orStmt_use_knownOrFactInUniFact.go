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
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) verOrStmt_UseOrInUniFactMem(stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	nextState := state.GetAddRound()

	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.orFact_UseOrInUniFactMem_atCurEnv(curEnv, stmt, nextState)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.orFact_UseOrInUniFactMem_atCurEnv(curEnv, stmt, nextState)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.orFact_UseOrInUniFactMem_atCurEnv(&curEnv, stmt, nextState)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) orFact_UseOrInUniFactMem_atCurEnv(curEnv *env.EnvMemory, stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	key := string(stmt.Facts[0].GetPropName())
	knownOrFacts, got := curEnv.OrFactInUniFactMem[key]
	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	for _, knownOrFactInUniFact := range knownOrFacts {
		ret := ver.useKnownOrFactInUniFactToCheckGivenOrFact(stmt, knownOrFactInUniFact, state)
		if ret.IsTrue() || ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) useKnownOrFactInUniFactToCheckGivenOrFact(given *ast.OrStmt, knownOrFactInUni *env.OrFactInUniFact, state *VerState) *glob.VerRet {
	if len(given.Facts) != len(knownOrFactInUni.OrFact.Facts) {
		return glob.NewEmptyVerRetUnknown()
	}

	for i := range given.Facts {
		if given.Facts[i].GetPropName().String() != knownOrFactInUni.OrFact.Facts[i].GetPropName().String() || given.Facts[i].GetFactType() != knownOrFactInUni.OrFact.Facts[i].GetFactType() {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	givenParams := []ast.Obj{}
	knownParams := []ast.Obj{}
	for i := range given.Facts {
		switch asStmt := given.Facts[i].(type) {
		case *ast.PureSpecificFactStmt:
			givenParams = append(givenParams, asStmt.Params...)
			knownParams = append(knownParams, knownOrFactInUni.OrFact.Facts[i].(*ast.PureSpecificFactStmt).Params...)
		case *ast.ExistSpecificFactStmt:
			givenParams, knownParams, _, _, ret := ver.GetParamsFromExistFactForMatchUniFactParams(asStmt, knownOrFactInUni.OrFact.Facts[i].(*ast.ExistSpecificFactStmt), []string{})
			if ret.IsNotTrue() {
				return ret
			}

			givenParams = append(givenParams, givenParams...)
			knownParams = append(knownParams, knownParams...)
		}
	}

	ok, uniConMap, err := ver.matchUniFactParamsWithSpecFactParams(knownParams, knownOrFactInUni.UniFact.Params, givenParams)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, knownOrFactInUni.OrFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	for _, param := range knownOrFactInUni.UniFact.Params {
		if _, ok := uniConMap[param]; !ok {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	// 真的对应上了
	for i := range given.Facts {
		switch asStmt := given.Facts[i].(type) {
		case *ast.PureSpecificFactStmt:
			if len(asStmt.Params) != len(knownOrFactInUni.OrFact.Facts[i].(*ast.PureSpecificFactStmt).Params) {
				return glob.NewEmptyVerRetUnknown()
			}

			for j := range asStmt.Params {
				givenParam, err := asStmt.Params[j].Instantiate(uniConMap)
				if err != nil {
					return glob.NewEmptyVerRetUnknown()
				}

				knownParam, err := knownOrFactInUni.OrFact.Facts[i].(*ast.PureSpecificFactStmt).Params[j].Instantiate(uniConMap)
				if err != nil {
					return glob.NewEmptyVerRetUnknown()
				}

				ret := ver.VerFactStmt(ast.NewEqualFact(givenParam, knownParam), state)
				if ret.IsNotTrue() {
					return glob.NewEmptyVerRetUnknown()
				}
			}

		case *ast.ExistSpecificFactStmt:
			instGiven, err := asStmt.Instantiate(uniConMap)
			if err != nil {
				return glob.NewEmptyVerRetUnknown()
			}
			instKnown, err := knownOrFactInUni.OrFact.Facts[i].Instantiate(uniConMap)
			if err != nil {
				return glob.NewEmptyVerRetUnknown()
			}

			if instGiven.String() != instKnown.String() {
				return glob.NewEmptyVerRetUnknown()
			}
		}
	}

	// 让dom和paramSet都成立
	for _, domFact := range knownOrFactInUni.UniFact.DomFacts {
		instDomFact, err := domFact.Instantiate(uniConMap)
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, domFact.String(), glob.BuiltinLine0, []string{err.Error()})
		}
		verRet := ver.VerFactStmt(instDomFact.(ast.FactStmt), state)
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	newUniMap := map[string]ast.Obj{}
	for i, paramSet := range knownOrFactInUni.UniFact.ParamSets {
		instParamSet, err := paramSet.Instantiate(newUniMap)
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, paramSet.String(), glob.BuiltinLine0, []string{err.Error()})
		}
		verRet := ver.VerFactStmt(ast.NewInFactWithObj(uniConMap[knownOrFactInUni.UniFact.Params[i]], instParamSet.(ast.Obj)), state)
		if verRet.IsNotTrue() {
			return verRet
		}
		newUniMap[knownOrFactInUni.UniFact.Params[i]] = uniConMap[knownOrFactInUni.UniFact.Params[i]]
	}

	return glob.NewEmptyVerRetTrue()
}
