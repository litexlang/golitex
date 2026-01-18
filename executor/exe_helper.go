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
	"slices"
)

func notOkExec(state *glob.StmtRet, err error) bool {
	if err != nil {
		return true
	}
	if state.IsUnknown() || state.IsErr() {
		return true
	}
	return false
}

func (exec *Executor) NewCommutativeProp(specFact *ast.SpecFactStmt) {
	if _, ok := exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)]; !ok {
		exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)] = env.NewCommutativePropMemItemStruct()
	}

	switch specFact.FactType {
	case ast.TruePure:
		exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)].TruePureIsCommutative = true
	case ast.FalsePure:
		exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)].FalsePureIsCommutative = true
	default:
		panic("not implemented: not commutative prop")
	}
}

func (exec *Executor) verifyFactsAtCurEnv(proofs []ast.FactStmt, verState *VerState) (*glob.StmtRet, ast.Stmt, error) {
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
			return glob.ErrRet(ret.String()), proof, fmt.Errorf(ret.String())
		}
	}
	return glob.NewEmptyStmtTrue(), nil, nil
}

// func (exec *Executor) GetBuiltinEnv() *env.EnvMemory {
// 	return exec.Env.GetUpMostEnv()
// }

// func (exec *Executor) GetSecondUpMostEnv() *env.EnvMemory {
// 	return exec.Env.GetSecondUpMostEnv()
// }

func checkParamsInFnDefNotDefinedAndParamSetsDefined(exec *Executor, params []string, paramSets []ast.Obj) *glob.ShortRet {
	for _, paramSet := range paramSets {
		ret := exec.Env.LookupNamesInObj(paramSet, map[string]struct{}{})
		if ret.IsNotTrue() {
			return glob.NewShortRetErr(ret.String())
		}
	}

	for _, param := range params {
		ret := exec.Env.LookupNamesInObj(ast.Atom(param), map[string]struct{}{})
		if ret.IsTrue() {
			return glob.NewShortRetErr(fmt.Sprintf("parameter %s is already defined. To avoid ambiguity, please use a different name for the parameter", param))
		}
	}

	return glob.NewEmptyShortTrueRet()
}

func (exec *Executor) declareParamsAndDomFactsInUniFact(stmt *ast.UniFactStmt) *glob.StmtRet {
	// declare parameters in asUnivFact in the env
	objDefStmt := ast.NewDefLetStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts.Copy(), stmt.Line)

	execState := exec.defLetStmt(objDefStmt)
	if execState.IsNotTrue() {
		return execState.AddError(fmt.Sprintf("Claim statement error: Failed to declare parameters in universal fact:\n%s\n", objDefStmt))
	}

	return glob.NewEmptyStmtTrue()
}

func (exec *Executor) GenerateShortExistFact(specFact *ast.SpecFactStmt) *ast.ExistStFactStruct {
	lenOfParams := len(specFact.Params)
	randomParams := []string{}
	for i := 0; i < lenOfParams; i++ {
		for {
			randomObj := ast.Atom(exec.Env.GenerateUndeclaredRandomName())
			if !slices.Contains(randomParams, string(randomObj)) {
				randomParams = append(randomParams, string(randomObj))
				break
			}
		}
	}

	randomParamSets := []ast.Obj{}
	for i := 0; i < len(randomParams); i++ {
		randomParamSets = append(randomParamSets, ast.Atom(glob.KeywordSet))
	}

	randomParamAsObj := []ast.Obj{}
	for i := 0; i < len(randomParams); i++ {
		randomParamAsObj = append(randomParamAsObj, ast.Atom(randomParams[i]))
	}

	return ast.NewExistStFactStruct(ast.TrueExist_St, specFact.PropName, specFact.IsTrue(), randomParams, randomParamSets, randomParamAsObj, specFact.Line)
}
