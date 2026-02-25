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
	env "golitex/environment"
	glob "golitex/glob"
	"runtime"
)

func notOkExec(state ast.StmtRet, err error) bool {
	if err != nil {
		return true
	}
	if state.IsUnknown() || state.IsErr() {
		return true
	}
	return false
}

func (exec *Executor) NewCommutativeProp(specFact *ast.PureSpecificFactStmt) {
	if _, ok := exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)]; !ok {
		exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)] = env.NewCommutativePropMemItemStruct()
	}

	switch specFact.IsTrue {
	case true:
		exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)].TruePureIsCommutative = true
	case false:
		exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)].FalsePureIsCommutative = true
	default:
		panic("not implemented: not commutative prop")
	}
}

func (exec *Executor) verifyFactsAtCurEnv(proofs []ast.FactStmt, verState *VerState) (ast.StmtRet, ast.Stmt, error) {
	ver := NewVerifier(exec.Env)
	for _, proof := range proofs {
		verRet := ver.VerFactStmt(proof, verState)
		if verRet.IsErr() {
			return verRet.ToStmtRet(), proof, fmt.Errorf(verRet.String())
		} else if verRet.IsUnknown() {
			return verRet.ToStmtRet(), proof, nil
		}

		ret := exec.Env.NewFactWithCheckingNameDefined(proof)
		if ret.IsErr() {
			return ast.StmtErrRet(proof, ret.String()), proof, fmt.Errorf(ret.String())
		}
	}
	return newTrueStmtRetWithCaller(), nil, nil
}

// func (exec *Executor) GetBuiltinEnv() *env.EnvMemory {
// 	return exec.Env.GetUpMostEnv()
// }

// func (exec *Executor) GetSecondUpMostEnv() *env.EnvMemory {
// 	return exec.Env.GetSecondUpMostEnv()
// }

func checkParamsInFnDefNotDefinedAndParamSetsDefined(exec *Executor, params []string, paramSets []ast.Obj) ast.ShortRet {
	for _, paramSet := range paramSets {
		ret := exec.Env.LookupNamesInObj(paramSet, map[string]struct{}{})
		if ret.IsNotTrue() {
			return ast.NewErrShortRetWithMsg(ret.String())
		}
	}

	for _, param := range params {
		ret := exec.Env.LookupNamesInObj(ast.Atom(param), map[string]struct{}{})
		if ret.IsTrue() {
			return ast.NewErrShortRetWithMsg(fmt.Sprintf("parameter %s is already defined. To avoid ambiguity, please use a different name for the parameter", param))
		}
	}

	return ast.NewTrueShortRet()
}

// func (exec *Executor) declareParamsAndDomFactsInUniFact(stmt *ast.UniFactStmt) ast.StmtRet{
// 	// declare parameters in asUnivFact in the env
// 	objDefStmt := ast.NewDefLetStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts.Copy(), stmt.Line)

// 	execState := exec.defLetStmt(objDefStmt)
// 	if execState.IsNotTrue() {
// 		return execState.AddError(fmt.Sprintf("Claim statement error: Failed to declare parameters in universal fact:\n%s\n", objDefStmt))
// 	}

// 	return glob.NewEmptyStmtTrue()
// }

// func (exec *Executor) GenerateShortExistFact(specFact *ast.ExistSpecificFactStmt) *ast.ExistSpecificFactStmt {
// 	lenOfParams := len(specFact.Params)
// 	randomParams := []string{}
// 	for i := 0; i < lenOfParams; i++ {
// 		for {
// 			randomObj := ast.Atom(exec.Env.GenerateUndeclaredRandomName())
// 			if !slices.Contains(randomParams, string(randomObj)) {
// 				randomParams = append(randomParams, string(randomObj))
// 				break
// 			}
// 		}
// 	}

// 	randomParamSets := []ast.Obj{}
// 	for i := 0; i < len(randomParams); i++ {
// 		randomParamSets = append(randomParamSets, ast.Atom(glob.KeywordSet))
// 	}

// 	randomParamAsObj := []ast.Obj{}
// 	for i := 0; i < len(randomParams); i++ {
// 		randomParamAsObj = append(randomParamAsObj, ast.Atom(randomParams[i]))
// 	}

// 	return ast.NewExistSpecificFactStmt(true, randomParams, randomParamSets, ast.NewPureSpecificFactStmt(specFact.IsTrue, specFact.PropName, specFact, specFact.Line), specFact.Line)
// }

func (exec *Executor) NewErrStmtRet(stmt ast.Stmt) ast.StmtRet {
	ret := ast.NewErrStmtEmptyRet(stmt)
	return ret
}

func (exec *Executor) NewTrueStmtRet(stmt ast.Stmt) ast.StmtRet {
	ret := ast.NewTrueStmtEmptyRet(stmt)
	return ret
}

// getCallerFuncName returns the name of the function that called the current function
func getCallerFuncName() string {
	pc, _, _, ok := runtime.Caller(2)
	if !ok {
		return "unknown"
	}
	fn := runtime.FuncForPC(pc)
	if fn == nil {
		return "unknown"
	}
	return fn.Name()
}

// helper functions to create StmtRet with nil stmt and caller function name
func newErrStmtRetWithCaller(msg string) ast.StmtRet {
	caller := getCallerFuncName()
	return ast.NewErrStmtEmptyRet(nil).AddExtraInfo(fmt.Sprintf("[Called from: %s]\n", caller))
}

func newTrueStmtRetWithCaller() ast.StmtRet {
	caller := getCallerFuncName()
	return ast.NewTrueStmtEmptyRet(nil).AddExtraInfo(fmt.Sprintf("[Called from: %s]\n", caller))
}

func newUnknownStmtRetWithCaller(msg string) ast.StmtRet {
	caller := getCallerFuncName()
	return ast.NewUnknownStmtEmptyRet(nil).AddExtraInfo(fmt.Sprintf("[Called from: %s]\n%s", caller, msg))
}

func stmtErrRetWithCaller(msg string) ast.StmtRet {
	caller := getCallerFuncName()
	return ast.StmtErrRet(nil, msg).AddExtraInfo(fmt.Sprintf("[Called from: %s]\n", caller))
}

func (ver *Verifier) replaceUniFactParamsWithRandomParams(stmt *ast.UniFactStmt) (*ast.UniFactStmt, error) {
	indexesOfParamsToReplace := []int{}
	for i, param := range stmt.Params {
		if ok := ver.Env.IsValidAndAvailableName(param); !ok {
			indexesOfParamsToReplace = append(indexesOfParamsToReplace, i)
		}
	}

	if len(indexesOfParamsToReplace) == 0 {
		return stmt, nil
	}

	randomParams := ver.Env.GenerateNUnusedRandomNames(len(indexesOfParamsToReplace))
	uniMap := make(map[string]ast.Obj)
	for i, index := range indexesOfParamsToReplace {
		uniMap[stmt.Params[index]] = ast.Atom(randomParams[i])
	}

	newParamSets := []ast.Obj{}
	for _, index := range indexesOfParamsToReplace {
		newParamSets = append(newParamSets, stmt.ParamSets[index])
	}

	newDomFacts := []ast.Spec_OrFact{}
	for _, domFact := range stmt.DomFacts {
		newDomFact, err := domFact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newDomFact.(ast.Spec_OrFact))
	}

	newThenFacts := []ast.Spec_OrFact{}
	for _, thenFact := range stmt.ThenFacts {
		newThenFact, err := thenFact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newThenFacts = append(newThenFacts, newThenFact.(ast.Spec_OrFact))
	}

	newParams := []string{}
	for _, param := range stmt.Params {
		if _, ok := uniMap[param]; ok {
			newParams = append(newParams, string(uniMap[param].(ast.Atom)))
		} else {
			newParams = append(newParams, param)
		}
	}

	return ast.NewUniFact(newParams, newParamSets, newDomFacts, newThenFacts, stmt.Line), nil
}

func (ver *Verifier) declareParamsInUniFactAndCheckFnReqOfParamSetsAndDoms(fact *ast.UniFactStmt, state *VerState) ast.StmtRet {
	ret := ver.declareParamsAndCheckFnReqOfParamSets(fact.Params, fact.ParamSets, state)
	if ret.IsNotTrue() {
		return ast.StmtErrRet(fact, ret.String())
	}

	// check fn req inside dom facts
	ret = ver.checkFnReqInsideReversibleFacts(fact.DomFacts, state)
	if ret.IsNotTrue() {
		return ast.StmtErrRet(fact, ret.String())
	}

	return ast.NewTrueStmtEmptyRet(fact)
}

func (ver *Verifier) declareParamsAndCheckFnReqOfParamSets(params []string, paramSets []ast.Obj, state *VerState) ast.VerRet {
	for i := range params {
		if !glob.IsKeywordSetOrNonEmptySetOrFiniteSet(paramSets[i].String()) {
			ret := ver.checkFnReqOfObj(paramSets[i], state)
			if ret.IsNotTrue() {
				return ret
			}
		}

		letStmt := ast.NewDefLetStmt([]string{params[i]}, []ast.Obj{paramSets[i]}, []ast.FactStmt{}, glob.BuiltinLine0)
		ret2 := ver.Env.DefLetStmt(letStmt)
		if ret2.IsErr() {
			return ast.NewErrVerRet(nil).AddExtraInfo(ret2.String())
		}
	}
	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) declareParamsInDefPropAndCheckFnReqOfParamSets(stmt *ast.DefPropStmt, state *VerState) ast.VerRet {
	verRet := ver.declareParamsAndCheckFnReqOfParamSets(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, state)
	return verRet
}

func (ver *Verifier) replaceParamsInDefPropWithRandomParams(stmt *ast.DefPropStmt) (*ast.DefPropStmt, error) {
	indexesOfParamsToReplace := []int{}
	for i, param := range stmt.DefHeader.Params {
		if ok := ver.Env.IsValidAndAvailableName(param); !ok {
			indexesOfParamsToReplace = append(indexesOfParamsToReplace, i)
		}
	}

	if len(indexesOfParamsToReplace) == 0 {
		return stmt, nil
	}

	randomParams := ver.Env.GenerateNUnusedRandomNames(len(indexesOfParamsToReplace))
	uniMap := make(map[string]ast.Obj)
	for i, index := range indexesOfParamsToReplace {
		uniMap[stmt.DefHeader.Params[index]] = ast.Atom(randomParams[i])
	}

	// 实例化 DefHeader.ParamSets
	newParamSets := []ast.Obj{}
	for _, paramSet := range stmt.DefHeader.ParamSets {
		newParamSet, err := paramSet.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParamSets = append(newParamSets, newParamSet)
	}

	// 更新 Params 列表
	newParams := []string{}
	for _, param := range stmt.DefHeader.Params {
		if _, ok := uniMap[param]; ok {
			newParams = append(newParams, string(uniMap[param].(ast.Atom)))
		} else {
			newParams = append(newParams, param)
		}
	}

	newDefHeader := ast.NewDefHeader(stmt.DefHeader.Name, newParams, newParamSets)

	// 实例化 IffFactsOrNil
	newIffFacts := []ast.FactStmt{}
	for _, fact := range stmt.IffFactsOrNil {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact)
	}

	// 实例化 ImplicationFactsOrNil
	instantiatedThenFacts, err := stmt.ImplicationFactsOrNil.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	return ast.NewDefPropStmt(newDefHeader, newIffFacts, instantiatedThenFacts, stmt.Line), nil
}
