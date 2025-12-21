// // Copyright 2024 Jiachen Shen.
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// //     http://www.apache.org/licenses/LICENSE-2.0
// //
// // Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// // Litex email: <litexlang@outlook.com>
// // Litex website: https://litexlang.com
// // Litex github repository: https://github.com/litexlang/golitex
// // Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

// import (
// 	ast "golitex/ast"
// )

// func (env *Env) MakeUniFactParamsInThisDefPropDoNotConflictWithEnv(defPropStmt *ast.DefPropStmt) *ast.DefPropStmt {
// 	newDomFacts := []ast.FactStmt{}
// 	for _, domFact := range defPropStmt.DomFactsOrNil {
// 		newDomFacts = append(newDomFacts, env.makeUniFactParamsInThisFactDoNotConflictWithEnv(domFact))
// 	}

// 	newIffFacts := []ast.FactStmt{}
// 	for _, iffFact := range defPropStmt.IffFactsOrNil {
// 		newIffFacts = append(newIffFacts, env.makeUniFactParamsInThisFactDoNotConflictWithEnv(iffFact))
// 	}

// 	newThenFacts := []ast.FactStmt{}
// 	for _, thenFact := range defPropStmt.ImplicationFactsOrNil {
// 		newThenFacts = append(newThenFacts, env.makeUniFactParamsInThisFactDoNotConflictWithEnv(thenFact))
// 	}

// 	return ast.NewDefPropStmt(defPropStmt.DefHeader, newDomFacts, newIffFacts, newThenFacts, defPropStmt.Line)
// }

// func (env *Env) makeUniFactParamsInThisFactDoNotConflictWithEnv(fact ast.FactStmt) ast.FactStmt {
// 	switch asFact := fact.(type) {
// 	case *ast.UniFactStmt:
// 		return env.makeUniFactParamsInThisUniFactDoNotConflictWithEnv(asFact)
// 	case *ast.UniFactWithIffStmt:
// 		return env.makeUniFactWithIffParamsInThisUniFactDoNotConflictWithEnv(asFact)
// 	default:
// 		return fact
// 	}
// }

// func (env *Env) makeUniFactParamsInThisUniFactDoNotConflictWithEnv_getNewParamsAndParamSets(params []string, paramSets []ast.Obj) ([]string, []ast.Obj, map[string]ast.Obj) {
// 	conflictingParams := map[string]struct{}{}
// 	for _, param := range params {
// 		ret := env.IsNameDefinedOrBuiltin(param, map[string]struct{}{})
// 		if ret.IsTrue() {
// 			conflictingParams[param] = struct{}{}
// 		}
// 	}

// 	if len(conflictingParams) == 0 {
// 		return params, paramSets, map[string]ast.Obj{}
// 	}

// 	// get non conflicting params
// 	newParams := []string{}
// 	newParamsSet := map[string]struct{}{}
// 	newParamSlice := []ast.Obj{}
// 	formerParamToNewParamMap := map[string]ast.Obj{}

// 	for i, param := range params {
// 		// inst param sets
// 		if i > 0 {
// 			curSet := paramSets[i]
// 			instantiatedCurSet, err := curSet.Instantiate(formerParamToNewParamMap)
// 			if err != nil {
// 				panic(err)
// 			}
// 			newParamSlice = append(newParamSlice, instantiatedCurSet)
// 		} else {
// 			newParamSlice = append(newParamSlice, paramSets[i])
// 		}

// 		if _, ok := conflictingParams[param]; !ok {
// 			newParams = append(newParams, param)
// 			newParamsSet[param] = struct{}{}
// 			formerParamToNewParamMap[param] = ast.Atom(param)
// 		} else {
// 			newParam := env.GenerateUndeclaredRandomName_AndNotInMap(newParamsSet)
// 			newParams = append(newParams, newParam)
// 			newParamsSet[newParam] = struct{}{}
// 			formerParamToNewParamMap[param] = ast.Atom(newParam)
// 		}
// 	}

// 	return newParams, newParamSlice, formerParamToNewParamMap
// }

// func (env *Env) makeUniFactParamsInThisUniFactDoNotConflictWithEnv(uniFact *ast.UniFactStmt) *ast.UniFactStmt {
// 	newParams, newParamSets, formerParamToNewParamMap := env.makeUniFactParamsInThisUniFactDoNotConflictWithEnv_getNewParamsAndParamSets(uniFact.Params, uniFact.ParamSets)

// 	if len(formerParamToNewParamMap) == 0 {
// 		return uniFact
// 	}

// 	newDomFacts, err := uniFact.DomFacts.InstantiateFact(formerParamToNewParamMap)
// 	if err != nil {
// 		panic(err)
// 	}

// 	// inst then facts
// 	newThenFacts, err := uniFact.ThenFacts.InstantiateFact(formerParamToNewParamMap)
// 	if err != nil {
// 		panic(err)
// 	}

// 	return ast.NewUniFact(newParams, newParamSets, newDomFacts, newThenFacts, uniFact.Line)
// }

// func (env *Env) makeUniFactWithIffParamsInThisUniFactDoNotConflictWithEnv(uniFact *ast.UniFactWithIffStmt) *ast.UniFactWithIffStmt {
// 	newParams, newParamSets, formerParamToNewParamMap := env.makeUniFactParamsInThisUniFactDoNotConflictWithEnv_getNewParamsAndParamSets(uniFact.UniFact.Params, uniFact.UniFact.ParamSets)

// 	if len(formerParamToNewParamMap) == 0 {
// 		return uniFact
// 	}

// 	newDomFacts, err := uniFact.UniFact.DomFacts.InstantiateFact(formerParamToNewParamMap)
// 	if err != nil {
// 		panic(err)
// 	}

// 	newThenFacts, err := uniFact.UniFact.ThenFacts.InstantiateFact(formerParamToNewParamMap)
// 	if err != nil {
// 		panic(err)
// 	}

// 	newIffFacts, err := uniFact.IffFacts.InstantiateFact(formerParamToNewParamMap)
// 	if err != nil {
// 		panic(err)
// 	}

// 	return ast.NewUniFactWithIff(ast.NewUniFact(newParams, newParamSets, newDomFacts, newThenFacts, uniFact.UniFact.Line), newIffFacts, uniFact.Line)
// }
