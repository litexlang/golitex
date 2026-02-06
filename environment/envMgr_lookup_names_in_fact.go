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
	"maps"
)

func (envMgr *EnvMgr) LookUpNamesInFact(stmt ast.FactStmt, extraParams map[string]struct{}) ast.ShortRet {
	switch s := stmt.(type) {
	case ast.SpecificFactStmt:
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
		return ast.NewErrShortRetWithMsg(fmt.Sprintf("unknown fact type: %T", stmt))
	}
}

func (envMgr *EnvMgr) LookupNamesInSpecFact(stmt ast.SpecificFactStmt, extraParams map[string]struct{}) ast.ShortRet {
	switch asFact := stmt.(type) {
	case *ast.PureSpecificFactStmt:
		return envMgr.lookupNamesInPureFact(asFact, extraParams)
	case *ast.ExistSpecificFactStmt:
		return envMgr.lookupNamesInExistFact(asFact, extraParams)
	default:
		return ast.NewErrShortRetWithMsg(fmt.Sprintf("unknown specific fact type: %T", stmt))
	}
}

func (envMgr *EnvMgr) lookupNamesInExistFact(stmt *ast.ExistSpecificFactStmt, extraParams map[string]struct{}) ast.ShortRet {
	if ret := envMgr.IsPropDefinedOrBuiltinProp(stmt.PureFact); ret.IsNotTrue() {
		return ast.NewErrShortRetWithMsg(fmt.Sprintf("exist fact prop %s is not defined or builtin prop", stmt.PureFact.PropName))
	}

	newExtraParams := maps.Clone(extraParams)
	for i, paramSet := range stmt.ExistFreeParams {
		if envMgr.lookupAtomObjName(ast.Atom(stmt.ExistFreeParams[i]), extraParams).IsTrue() {
			return ast.NewErrShortRetWithMsg(fmt.Sprintf("failed to lookup name %s in exist fact exist parameter %s", stmt.ExistFreeParams[i], paramSet))
		}
		newExtraParams[stmt.ExistFreeParams[i]] = struct{}{}
	}

	// // check paramSet
	// for i, paramSet := range stmt.ExistFreeParamSets {
	// 	ret := envMgr.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(paramSet, newExtraParams)
	// 	if ret.IsNotTrue() {
	// 		return ret
	// 	}

	// 	newExtraParams[stmt.ExistFreeParams[i]] = struct{}{}
	// }

	for _, param := range stmt.PureFact.Params {
		if envMgr.LookupNamesInObj(param, newExtraParams).IsNotTrue() {
			return ast.NewErrShortRetWithMsg(fmt.Sprintf("failed to lookup name %s in exist fact exist parameter %s", param.String(), param.String()))
		}
	}

	return ast.NewTrueShortRet()
}

func (envMgr *EnvMgr) lookupNamesInPureFact(stmt *ast.PureSpecificFactStmt, extraParams map[string]struct{}) ast.ShortRet {
	if ret := envMgr.IsPropDefinedOrBuiltinProp(stmt); ret.IsNotTrue() {
		return ast.NewErrShortRetWithMsg(fmt.Sprintf("failed to lookup names in pure fact prop %s", stmt.PropName)).AddExtraInfo(ret.String())
	}

	for _, param := range stmt.Params {
		if envMgr.LookupNamesInObj(param, extraParams).IsNotTrue() {
			return ast.NewErrShortRetWithMsg(fmt.Sprintf("failed to lookup names in pure fact parameter %s", param.String()))
		}
	}

	return ast.NewTrueShortRet()
}

func (envMgr *EnvMgr) IsPropDefinedOrBuiltinProp(stmt *ast.PureSpecificFactStmt) ast.StmtRet {
	if glob.IsBuiltinPropName(string(stmt.PropName)) {
		return ast.NewTrueStmtEmptyRet(stmt)
	}

	// Check if it's a regular prop defined by user
	_, ok := envMgr.GetPropDef(stmt.GetPropName())
	if ok {
		return ast.NewTrueStmtEmptyRet(stmt)
	}

	// existPropDef := envMgr.GetExistPropDef(stmt.PropName)
	// if existPropDef != nil {
	// 	return glob.NewEmptyStmtTrue()
	// }

	return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("undefined prop or exist_prop: %s", stmt.PropName))
	// }
}

func (envMgr *EnvMgr) LookupNamesInUniFact(stmt *ast.UniFactStmt, extraParams map[string]struct{}) ast.ShortRet {
	// Merge stmt.Params into extraParams for this uni fact
	combinedParams := make(map[string]struct{})
	for k, v := range extraParams {
		combinedParams[k] = v
	}

	// Check param sets
	for i, paramSet := range stmt.ParamSets {
		ret := envMgr.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(paramSet, combinedParams)
		if ret.IsNotTrue() {
			return ast.NewErrShortRetWithMsg(fmt.Sprintf("param set %s conflicts with defined parameter", paramSet.String()))
		}

		if _, ok := combinedParams[stmt.Params[i]]; ok {
			return ast.NewErrShortRetWithMsg(fmt.Sprintf("duplicate free parameter: %s", stmt.Params[i]))
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

	return ast.NewTrueShortRet()
}

func (envMgr *EnvMgr) LookupNamesInUniFactWithIff(stmt *ast.UniFactWithIffStmt, extraParams map[string]struct{}) ast.ShortRet {
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

	return ast.NewTrueShortRet()
}

func (envMgr *EnvMgr) LookupNamesInOrFact(stmt *ast.OrStmt, extraParams map[string]struct{}) ast.ShortRet {
	for _, stmt := range stmt.Facts {
		if ret := envMgr.LookUpNamesInFact(stmt, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return ast.NewTrueShortRet()
}

func (envMgr *EnvMgr) LookupNamesInEqualsFact(stmt *ast.EqualsFactStmt, extraParams map[string]struct{}) ast.ShortRet {
	for _, obj := range stmt.Params {
		if envMgr.LookupNamesInObj(obj, extraParams).IsNotTrue() {
			return ast.NewErrShortRetWithMsg(fmt.Sprintf("equals fact parameter %s conflicts with defined parameter", obj.String()))
		}
	}

	return ast.NewTrueShortRet()
}

func (envMgr *EnvMgr) LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(obj ast.Obj, extraParams map[string]struct{}) ast.ShortRet {
	if asAtom, ok := obj.(ast.Atom); ok && glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(asAtom)) {
		return ast.NewTrueShortRet()
	}

	return envMgr.LookupNamesInObj(obj, extraParams)
}
