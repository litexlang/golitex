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
	"strings"
)

// Helper methods for EnvMgr to access definitions

func (envMgr *EnvMgr) GetPropDef(propName ast.Atom) *ast.DefPropStmt {
	// depth
	propDef, ok := envMgr.AllDefinedPropNames[string(propName)]
	if ok {
		return propDef
	}
	return nil
}

func (envMgr *EnvMgr) GetExistPropDef(propName ast.Atom) *ast.DefExistPropStmt {
	existPropDef, ok := envMgr.AllDefinedExistPropNames[string(propName)]
	if ok {
		return existPropDef
	}
	return nil
}

func (envMgr *EnvMgr) IsPkgName(pkgName string) bool {
	_, ok := envMgr.PkgMgr.AbsPathNameMgr.NameAbsPathMap[pkgName]
	return ok
}

func (envMgr *EnvMgr) AtomsInObjDefinedOrBuiltin(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	switch asObj := obj.(type) {
	case ast.Atom:
		return envMgr.AtomObjDefinedOrBuiltin(asObj, extraParams)
	case *ast.FnObj:
		return envMgr.AtomsInFnObjDefinedOrBuiltin(asObj, extraParams)
	default:
		return glob.ErrRet(fmt.Errorf("unknown object type: %T", obj))
	}
}

// TODO: 目前只是检查了在当前的envMgr中是否定义了，没有检查在parent envMgr中是否定义了
func (envMgr *EnvMgr) AtomObjDefinedOrBuiltin(atom ast.Atom, extraParams map[string]struct{}) glob.GlobRet {
	if _, ok := extraParams[string(atom)]; ok {
		return glob.NewEmptyGlobTrue()
	}

	// Check if it's a builtin atom
	if glob.IsBuiltinAtom(string(atom)) {
		return glob.NewEmptyGlobTrue()
	}

	// Check if it's a number literal
	if _, ok := ast.IsNumLitAtomObj(atom); ok {
		return glob.NewEmptyGlobTrue()
	}

	// Check if it's defined by user
	ret := envMgr.IsAtomObjDefinedByUser(atom)
	if ret.IsTrue() {
		return glob.NewEmptyGlobTrue()
	}

	// Check if it's a keyword that's not an object
	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(atom)) {
		return glob.NewGlobErr(fmt.Sprintf("%s keyword is not an object.", string(atom)))
	} else {
		return glob.ErrRet(fmt.Errorf("undefined atom name: %s", atom))
	}
}

func (envMgr *EnvMgr) AtomsInFnObjDefinedOrBuiltin(fnObj *ast.FnObj, extraParams map[string]struct{}) glob.GlobRet {
	// Special handling for setBuilder
	if ast.IsSetBuilder(fnObj) {
		return envMgr.AtomsInSetBuilderDefined(fnObj, extraParams)
	}

	for _, param := range fnObj.Params {
		if ret := envMgr.AtomsInObjDefinedOrBuiltin(param, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	// 如果head是fn,那直接成立了
	if fnObj.HasAtomHeadEqualToStr(glob.KeywordFn) {
		return glob.NewEmptyGlobTrue()
	}

	// 如果head 是 fn_template 那也OK了
	if envMgr.FnObjHeadIsAtomAndIsFnSet(fnObj) {
		return glob.NewEmptyGlobTrue()
	}

	return envMgr.AtomsInObjDefinedOrBuiltin(fnObj.FnHead, extraParams)
}

func (envMgr *EnvMgr) AtomsInSetBuilderDefined(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	setBuilderObj := obj.(*ast.FnObj)
	setBuilder, err := setBuilderObj.ToSetBuilderStruct()
	if err != nil {
		return glob.ErrRet(fmt.Errorf("failed to parse setBuilder: %s", err.Error()))
	}

	// Check parentSet
	if ret := envMgr.AtomsInObjDefinedOrBuiltin(setBuilder.ParentSet, extraParams); ret.IsNotTrue() {
		return ret
	}

	// Merge setBuilder param into extraParams (it's a bound variable)
	combinedParams := make(map[string]struct{})
	for k, v := range extraParams {
		combinedParams[k] = v
	}
	combinedParams[setBuilder.Param] = struct{}{}

	// Check facts in setBuilder
	for _, fact := range setBuilder.Facts {
		if ret := envMgr.AtomsInSpecFactDefined(fact, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

// 在def时，检查fact中的所有atom是否都定义了
func (envMgr *EnvMgr) AtomObjsInFactProperlyDefined(stmt ast.FactStmt, extraParams map[string]struct{}) glob.GlobRet {
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
		if ret := envMgr.AtomsInObjDefinedOrBuiltin(param, extraParams); ret.IsNotTrue() {
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
		return envMgr.AtomObjDefinedOrBuiltin(atom, extraParams)
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
		if ret := envMgr.AtomObjsInFactProperlyDefined(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	for _, stmt := range stmt.ThenFacts {
		if ret := envMgr.AtomObjsInFactProperlyDefined(stmt, combinedParams); ret.IsNotTrue() {
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
		if ret := envMgr.AtomObjsInFactProperlyDefined(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) AtomsInOrDefined(stmt *ast.OrStmt, extraParams map[string]struct{}) glob.GlobRet {
	for _, stmt := range stmt.Facts {
		if ret := envMgr.AtomObjsInFactProperlyDefined(stmt, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) AtomsInEqualsFactDefined(stmt *ast.EqualsFactStmt, extraParams map[string]struct{}) glob.GlobRet {
	for _, obj := range stmt.Params {
		if ret := envMgr.AtomsInObjDefinedOrBuiltin(obj, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) IsAtomObjDefinedByUser(AtomObjName ast.Atom) glob.GlobRet {
	if strings.Contains(string(AtomObjName), glob.PkgNameAtomSeparator) {
		PkgNameAndAtomName := strings.Split(string(AtomObjName), glob.PkgNameAtomSeparator)
		PkgName := PkgNameAndAtomName[0]
		AtomName := PkgNameAndAtomName[1]
		pkgPath, ok := envMgr.PkgMgr.AbsPathNameMgr.NameAbsPathMap[PkgName]
		if !ok {
			return glob.ErrRet(fmt.Errorf("package %s is not found", PkgName))
		}
		pkgPathEnv, ok := envMgr.PkgMgr.AbsPkgPathEnvPairs[pkgPath]
		if !ok {
			return glob.ErrRet(fmt.Errorf("package environment for %s is not found", PkgName))
		}
		ret := pkgPathEnv.AtomObjDefinedOrBuiltin(ast.Atom(AtomName), make(map[string]struct{}))
		if ret.IsTrue() {
			return glob.NewEmptyGlobTrue()
		}
		return ret
	}

	// Search from current depth upward to depth 0
	_, ok := envMgr.AllDefinedAtomObjNames[string(AtomObjName)]
	if ok {
		return glob.NewEmptyGlobTrue()
	}

	// // TODO: 这里其实有点问题，应该独立出来，因为 fn_template 可能不能算 atom
	// if _, ok := envMgr.AllDefinedFnTemplateNames[string(AtomObjName)]; ok {
	// 	return glob.NewEmptyGlobTrue()
	// }

	return glob.ErrRet(fmt.Errorf("undefined: %s", AtomObjName))
}

func (envMgr *EnvMgr) AtomsInObjDefinedOrBuiltinOrSetNonemptySetFiniteSet(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	if asAtom, ok := obj.(ast.Atom); ok && glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(asAtom)) {
		return glob.NewEmptyGlobTrue()
	}

	return envMgr.AtomsInObjDefinedOrBuiltin(obj, extraParams)
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

	ret := envMgr.IsAtomObjDefinedByUser(ast.Atom(name))
	if ret.IsTrue() {
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

func (envMgr *EnvMgr) IsValidIdentifierAvailable(name string) glob.GlobRet {
	err := glob.IsValidUseDefinedAtomObj(name)
	if err != nil {
		return glob.ErrRet(err)
	}

	ret := envMgr.IsAtomObjDefinedByUser(ast.Atom(name))
	if ret.IsTrue() {
		return glob.ErrRet(duplicateDefError(name))
	}

	return glob.NewEmptyGlobTrue()
}
