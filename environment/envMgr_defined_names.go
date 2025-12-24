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
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// Helper methods for EnvMgr to access definitions

// 在def时，检查fact中的所有atom是否都定义了
func (envMgr *EnvMgr) NamesInFactProperlyDefined(stmt ast.FactStmt, extraParams map[string]struct{}) glob.GlobRet {
	switch s := stmt.(type) {
	case *ast.SpecFactStmt:
		return envMgr.AtomsInSpecFactDefined(s, extraParams)
	case *ast.UniFactStmt:
		return envMgr.AtomObjsInUniFactDefined(s, extraParams)
	case *ast.UniFactWithIffStmt:
		return envMgr.AtomsInUniFactWithIffDefined(s, extraParams)
	case *ast.OrStmt:
		return envMgr.AtomsInOrDefined(s, extraParams)
	case *ast.EqualsFactStmt:
		return envMgr.AtomsInEqualsFactDefined(s, extraParams)
	default:
		return glob.ErrRet(fmt.Errorf("unknown fact type: %T", stmt))
	}
}

func (envMgr *EnvMgr) AtomsInSpecFactDefined(stmt *ast.SpecFactStmt, extraParams map[string]struct{}) glob.GlobRet {
	if ret := envMgr.IsPropDefinedOrBuiltinProp(stmt); ret.IsNotTrue() {
		return ret
	}

	for _, param := range stmt.Params {
		if ret := envMgr.AtomObjNamesInObjDefinedOrBuiltin(param, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) IsPropDefinedOrBuiltinProp(stmt *ast.SpecFactStmt) glob.GlobRet {
	// Check if it's an exist_prop defined by user
	if stmt.TypeEnum == ast.TrueExist_St || stmt.TypeEnum == ast.FalseExist_St {
		if glob.IsBuiltinExistPropName(string(stmt.PropName)) {
			return glob.NewEmptyGlobTrue()
		}

		existPropDef := envMgr.GetExistPropDef(stmt.PropName)
		if existPropDef != nil {
			return glob.NewEmptyGlobTrue()
		}
		return glob.ErrRet(fmt.Errorf("undefined exist_prop: %s", stmt.PropName))
	} else {
		if glob.IsBuiltinPropName(string(stmt.PropName)) {
			return glob.NewEmptyGlobTrue()
		}

		if glob.IsBuiltinExistPropName(string(stmt.PropName)) {
			return glob.NewEmptyGlobTrue()
		}

		// Check if it's a regular prop defined by user
		propDef := envMgr.GetPropDef(stmt.PropName)
		if propDef != nil {
			return glob.NewEmptyGlobTrue()
		}

		existPropDef := envMgr.GetExistPropDef(stmt.PropName)
		if existPropDef != nil {
			return glob.NewEmptyGlobTrue()
		}

		return glob.ErrRet(fmt.Errorf("undefined prop or exist_prop: %s", stmt.PropName))
	}
}

func (envMgr *EnvMgr) IsAtomDefinedByOrBuiltinOrSetNonemptySetFiniteSet(atom ast.Atom, extraParams map[string]struct{}) glob.GlobRet {
	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(atom)) {
		return glob.NewEmptyGlobTrue()
	} else {
		return envMgr.IsDefinedOrBuiltinAtomObjName(atom, extraParams)
	}
}

func (envMgr *EnvMgr) AtomObjsInUniFactDefined(stmt *ast.UniFactStmt, extraParams map[string]struct{}) glob.GlobRet {
	// Merge stmt.Params into extraParams for this uni fact
	combinedParams := make(map[string]struct{})
	for k, v := range extraParams {
		combinedParams[k] = v
	}

	// Check param sets
	for i, paramSet := range stmt.ParamSets {
		ret := envMgr.AtomsInObjDefinedOrBuiltinOrSetNonemptySetFiniteSet(paramSet, combinedParams)
		if ret.IsNotTrue() {
			return ret
		}

		if _, ok := combinedParams[stmt.Params[i]]; ok {
			return glob.NewGlobErr(fmt.Sprintf("duplicate free parameter: %s", stmt.Params[i]))
		}
		combinedParams[stmt.Params[i]] = struct{}{}
	}

	for _, stmt := range stmt.DomFacts {
		if ret := envMgr.NamesInFactProperlyDefined(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	for _, stmt := range stmt.ThenFacts {
		if ret := envMgr.NamesInFactProperlyDefined(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) AtomsInUniFactWithIffDefined(stmt *ast.UniFactWithIffStmt, extraParams map[string]struct{}) glob.GlobRet {
	if ret := envMgr.AtomObjsInUniFactDefined(stmt.UniFact, extraParams); ret.IsNotTrue() {
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
		if ret := envMgr.NamesInFactProperlyDefined(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) AtomsInOrDefined(stmt *ast.OrStmt, extraParams map[string]struct{}) glob.GlobRet {
	for _, stmt := range stmt.Facts {
		if ret := envMgr.NamesInFactProperlyDefined(stmt, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) AtomsInEqualsFactDefined(stmt *ast.EqualsFactStmt, extraParams map[string]struct{}) glob.GlobRet {
	for _, obj := range stmt.Params {
		if ret := envMgr.AtomObjNamesInObjDefinedOrBuiltin(obj, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) AtomsInObjDefinedOrBuiltinOrSetNonemptySetFiniteSet(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	if asAtom, ok := obj.(ast.Atom); ok && glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(asAtom)) {
		return glob.NewEmptyGlobTrue()
	}

	return envMgr.AtomObjNamesInObjDefinedOrBuiltin(obj, extraParams)
}

func (envMgr *EnvMgr) IsNameDefinedOrBuiltin(name string, extraParams map[string]struct{}) glob.GlobRet {
	if _, ok := extraParams[name]; ok {
		return glob.NewEmptyGlobTrue()
	}

	if glob.IsBuiltinAtom(name) {
		return glob.NewEmptyGlobTrue()
	}

	if envMgr.IsPkgName(name) {
		return glob.NewEmptyGlobTrue()
	}

	if _, ok := ast.IsNumLitAtomObj(ast.Atom(name)); ok {
		return glob.NewEmptyGlobTrue()
	}

	defined := envMgr.IsAtomObjDefinedByUser(ast.Atom(name))
	if defined {
		return glob.NewEmptyGlobTrue()
	}

	existPropDef := envMgr.GetExistPropDef(ast.Atom(name))
	if existPropDef != nil {
		return glob.NewEmptyGlobTrue()
	}

	propDef := envMgr.GetPropDef(ast.Atom(name))
	if propDef != nil {
		return glob.NewEmptyGlobTrue()
	}

	return glob.ErrRet(fmt.Errorf("undefined: %s", name))
}

func (envMgr *EnvMgr) IsNameValidAndAvailable(name string) glob.GlobRet {
	err := glob.IsValidUseDefinedName(name)
	if err != nil {
		return glob.ErrRet(err)
	}

	defined := envMgr.IsAtomObjDefinedByUser(ast.Atom(name))
	if defined {
		return glob.ErrRet(duplicateDefError(name))
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) IsPkgName(pkgName string) bool {
	_, ok := envMgr.EnvPkgMgr.PkgMgr.NameAbsPathMap[pkgName]
	return ok
}
