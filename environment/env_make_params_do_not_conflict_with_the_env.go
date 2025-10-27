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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	ast "golitex/ast"
)

func (env *Env) MakeUniFactParamsInThisDefPropDoNotConflictWithEnv(defPropStmt *ast.DefPropStmt) *ast.DefPropStmt {
	newDomFacts := []ast.FactStmt{}
	for _, domFact := range defPropStmt.DomFacts {
		newDomFacts = append(newDomFacts, env.makeUniFactParamsInThisFactDoNotConflictWithEnv(domFact))
	}

	newIffFacts := []ast.FactStmt{}
	for _, iffFact := range defPropStmt.IffFacts {
		newIffFacts = append(newIffFacts, env.makeUniFactParamsInThisFactDoNotConflictWithEnv(iffFact))
	}

	newThenFacts := []ast.FactStmt{}
	for _, thenFact := range defPropStmt.ThenFacts {
		newThenFacts = append(newThenFacts, env.makeUniFactParamsInThisFactDoNotConflictWithEnv(thenFact))
	}

	return ast.NewDefPropStmt(defPropStmt.DefHeader, newDomFacts, newIffFacts, newThenFacts, defPropStmt.Line)
}

func (env *Env) makeUniFactParamsInThisFactDoNotConflictWithEnv(fact ast.FactStmt) ast.FactStmt {
	switch asFact := fact.(type) {
	case *ast.UniFactStmt:
		return env.makeUniFactParamsInThisUniFactDoNotConflictWithEnv(asFact)
	case *ast.UniFactWithIffStmt:
		panic("makeUniFactParamsInThisFactDoNotConflictWithEnv: UniFactWithIffStmt is not supported")
	default:
		return fact
	}
}

func (env *Env) makeUniFactParamsInThisUniFactDoNotConflictWithEnv(uniFact *ast.UniFactStmt) ast.FactStmt {
	conflictingParams := map[string]struct{}{}
	for _, param := range uniFact.Params {
		if env.IsAtomDeclared(ast.FcAtom(param), map[string]struct{}{}) {
			conflictingParams[param] = struct{}{}
		}
	}

	if len(conflictingParams) == 0 {
		return uniFact
	}

	// get non conflicting params
	newParams := []string{}
	newParamsMap := map[string]struct{}{}
	newParamSets := []ast.Fc{}

	formerParamToNewParamMap := map[string]ast.Fc{}
	for i, param := range uniFact.Params {
		// inst param sets
		if i > 0 {
			curSet := uniFact.ParamSets[i]
			instantiatedCurSet, err := curSet.Instantiate(formerParamToNewParamMap)
			if err != nil {
				panic(err)
			}
			newParamSets = append(newParamSets, instantiatedCurSet)
		} else {
			newParamSets = append(newParamSets, uniFact.ParamSets[i])
		}

		if _, ok := conflictingParams[param]; !ok {
			newParams = append(newParams, param)
			newParamsMap[param] = struct{}{}
			formerParamToNewParamMap[param] = ast.FcAtom(param)
		} else {
			newParam := env.GenerateUndeclaredRandomName_AndNotInMap(newParamsMap)
			newParams = append(newParams, newParam)
			newParamsMap[newParam] = struct{}{}
			formerParamToNewParamMap[param] = ast.FcAtom(newParam)
		}
	}

	newDomFacts := []ast.FactStmt{}
	for _, domFact := range uniFact.DomFacts {
		instantiatedDomFact, err := domFact.Instantiate(formerParamToNewParamMap)
		if err != nil {
			panic(err)
		}
		newDomFacts = append(newDomFacts, instantiatedDomFact)
	}

	// inst then facts
	newThenFacts := []ast.FactStmt{}
	for _, thenFact := range uniFact.ThenFacts {
		instantiatedThenFact, err := thenFact.Instantiate(formerParamToNewParamMap)
		if err != nil {
			panic(err)
		}
		newThenFacts = append(newThenFacts, instantiatedThenFact)
	}

	return ast.NewUniFact(newParams, newParamSets, newDomFacts, newThenFacts, uniFact.Line)
}
