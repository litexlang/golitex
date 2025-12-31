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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) LookUpNamesInFact(stmt ast.FactStmt, extraParams map[string]struct{}) *glob.StmtRet {
	switch s := stmt.(type) {
	case *ast.SpecFactStmt:
		return envMgr.LookupNamesInSpecFact(s, extraParams)
	case *ast.UniFactStmt:
		return envMgr.LookupNamesInUniFact(s, extraParams)
	case *ast.UniFactWithIffStmt:
		return envMgr.LookupNamesInUniFactWithIff(s, extraParams)
	case *ast.OrStmt:
		return envMgr.LookupNamesInOrFact(s, extraParams)
	case *ast.EqualsFactStmt:
		return envMgr.LookupNamesInEqualsFact(s, extraParams)
	default:
		return glob.ErrRet(fmt.Sprintf("unknown fact type: %T", stmt))
	}
}

func (envMgr *EnvMgr) LookupNamesInSpecFact(stmt *ast.SpecFactStmt, extraParams map[string]struct{}) *glob.StmtRet {
	switch stmt.FactType {
	case ast.TruePure:
		return envMgr.lookupNamesInPureFact(stmt, extraParams)
	case ast.FalsePure:
		return envMgr.lookupNamesInPureFact(stmt, extraParams)
	case ast.TrueExist_St:
		return envMgr.lookupNamesInExistFact(stmt, extraParams)
	case ast.FalseExist_St:
		return envMgr.lookupNamesInExistFact(stmt, extraParams)
	default:
		panic("")
	}
}

func (envMgr *EnvMgr) lookupNamesInExistFact(stmt *ast.SpecFactStmt, extraParams map[string]struct{}) *glob.StmtRet {
	if ret := envMgr.IsPropDefinedOrBuiltinProp(stmt); ret.IsNotTrue() {
		return ret
	}

	newExtraParams := map[string]struct{}{}
	for i := range extraParams {
		newExtraParams[i] = struct{}{}
	}

	existFactStruct := stmt.ToExistStFactStruct()

	for _, param := range existFactStruct.ExistFreeParams {
		if envMgr.lookupAtomObjName(ast.Atom(param), extraParams).IsTrue() {
			return glob.ErrRetWithErr(fmt.Errorf("exist fact exist parameter %s conflicts with defined parameter", param))
		}
	}

	// check paramSet
	for i, paramSet := range existFactStruct.ExistFreeParamSets {
		ret := envMgr.LookupNamesInObj(paramSet, newExtraParams)
		if ret.IsNotTrue() {
			return ret
		}

		newExtraParams[existFactStruct.ExistFreeParams[i]] = struct{}{}
	}

	for _, param := range stmt.Params {
		if ret := envMgr.LookupNamesInObj(param, newExtraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) lookupNamesInPureFact(stmt *ast.SpecFactStmt, extraParams map[string]struct{}) *glob.StmtRet {
	if ret := envMgr.IsPropDefinedOrBuiltinProp(stmt); ret.IsNotTrue() {
		return ret
	}

	for _, param := range stmt.Params {
		if ret := envMgr.LookupNamesInObj(param, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) IsPropDefinedOrBuiltinProp(stmt *ast.SpecFactStmt) *glob.StmtRet {
	// Check if it's an exist_prop defined by user
	// if stmt.FactType == ast.TrueExist_St || stmt.FactType == ast.FalseExist_St {
	// 	if glob.IsBuiltinExistPropName(string(stmt.PropName)) {
	// 		return glob.NewEmptyStmtTrue()
	// 	}

	// 	existPropDef := envMgr.GetExistPropDef(stmt.PropName)
	// 	if existPropDef != nil {
	// 		return glob.NewEmptyStmtTrue()
	// 	}
	// 	return glob.ErrRet(fmt.Sprintf("undefined exist_prop: %s", stmt.PropName))
	// } else {
	if glob.IsBuiltinPropName(string(stmt.PropName)) {
		return glob.NewEmptyStmtTrue()
	}

	if glob.IsBuiltinExistPropName(string(stmt.PropName)) {
		return glob.NewEmptyStmtTrue()
	}

	// Check if it's a regular prop defined by user
	propDef := envMgr.GetPropDef(stmt.PropName)
	if propDef != nil {
		return glob.NewEmptyStmtTrue()
	}

	existPropDef := envMgr.GetExistPropDef(stmt.PropName)
	if existPropDef != nil {
		return glob.NewEmptyStmtTrue()
	}

	return glob.ErrRet(fmt.Sprintf("undefined prop or exist_prop: %s", stmt.PropName))
	// }
}

func (envMgr *EnvMgr) LookupNamesInUniFact(stmt *ast.UniFactStmt, extraParams map[string]struct{}) *glob.StmtRet {
	// Merge stmt.Params into extraParams for this uni fact
	combinedParams := make(map[string]struct{})
	for k, v := range extraParams {
		combinedParams[k] = v
	}

	// Check param sets
	for i, paramSet := range stmt.ParamSets {
		ret := envMgr.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(paramSet, combinedParams)
		if ret.IsNotTrue() {
			return ret
		}

		if _, ok := combinedParams[stmt.Params[i]]; ok {
			return glob.ErrRet(fmt.Sprintf("duplicate free parameter: %s", stmt.Params[i]))
		}
		combinedParams[stmt.Params[i]] = struct{}{}
	}

	for _, stmt := range stmt.DomFacts {
		if ret := envMgr.LookUpNamesInFact(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	for _, stmt := range stmt.ThenFacts {
		if ret := envMgr.LookUpNamesInFact(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) LookupNamesInUniFactWithIff(stmt *ast.UniFactWithIffStmt, extraParams map[string]struct{}) *glob.StmtRet {
	if ret := envMgr.LookupNamesInUniFact(stmt.UniFact, extraParams); ret.IsNotTrue() {
		return ret
	}

	combinedParams := map[string]struct{}{}
	for k, v := range extraParams {
		combinedParams[k] = v
	}

	for _, v := range stmt.UniFact.Params {
		combinedParams[v] = struct{}{}
	}

	for _, stmt := range stmt.IffFacts {
		if ret := envMgr.LookUpNamesInFact(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) LookupNamesInOrFact(stmt *ast.OrStmt, extraParams map[string]struct{}) *glob.StmtRet {
	for _, stmt := range stmt.Facts {
		if ret := envMgr.LookUpNamesInFact(stmt, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) LookupNamesInEqualsFact(stmt *ast.EqualsFactStmt, extraParams map[string]struct{}) *glob.StmtRet {
	for _, obj := range stmt.Params {
		if ret := envMgr.LookupNamesInObj(obj, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(obj ast.Obj, extraParams map[string]struct{}) *glob.StmtRet {
	if asAtom, ok := obj.(ast.Atom); ok && glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(asAtom)) {
		return glob.NewEmptyStmtTrue()
	}

	return envMgr.LookupNamesInObj(obj, extraParams)
}
