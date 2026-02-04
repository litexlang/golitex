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
	"slices"
)

func (envMgr *EnvMgr) NewDefProp_InsideAtomsDeclared(stmt *ast.DefPropStmt) ast.StmtRet {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, string(stmt.DefHeader.Name)) {
		ret := ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name))
		return ret
	}

	ret := envMgr.IsValidAndAvailableName(string(stmt.DefHeader.Name))
	if !ret {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("invalid or unavailable name: %s", stmt.DefHeader.Name))
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefHeader.Name)] = struct{}{}

	for _, fact := range stmt.IffFactsOrNil {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("in iff fact of prop %s definition", stmt.DefHeader.Name))
		}
	}

	key := string(stmt.DefHeader.Name)

	// Save to AllDefinedPropNames
	envMgr.AllDefinedPropNames[key] = NewDefinedStuff(stmt, envMgr.CurEnvDepth())

	// Mark in current EnvSlice
	envMgr.CurEnv().PropDefMem[key] = struct{}{}

	return ast.NewTrueStmtEmptyRet(stmt)
}

func (envMgr *EnvMgr) AtomsInFnTemplateFnTemplateDeclared(name ast.Atom, stmt *ast.DefFnSetStmt) ast.StmtRet {
	// fn名不能和parameter名重叠
	if slices.Contains(stmt.TemplateDefHeader.Params, string(name)) {
		ret := ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("fn name %s cannot be the same as parameter name %s", name, name))
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.TemplateDefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}

	ret := envMgr.LookupNamesInObj(stmt.AnonymousFn.RetSet, extraAtomNames)
	if ret.IsErr() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("in return set of fn template %s", name))
	}

	extraAtomNames[string(name)] = struct{}{}

	for _, fact := range stmt.TemplateDomFacts {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("in template dom fact of fn %s definition", name))
		}
	}

	// ret = envMgr.NonDuplicateParam_NoUndeclaredParamSet_ExtraAtomNames(stmt.Fn.Params, stmt.Fn.ParamSets, extraAtomNames, false)
	// if ret.IsErr() {
	// 	return ret
	// }

	for _, param := range stmt.AnonymousFn.Params {
		extraAtomNames[param] = struct{}{}
	}

	for _, fact := range stmt.AnonymousFn.DomFacts {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("in dom fact of fn %s definition", name))
		}
	}

	for _, fact := range stmt.AnonymousFn.ThenFacts {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("in then fact of fn %s definition", name))
		}
	}

	return ast.NewTrueStmtEmptyRet(stmt)
}

// func (envMgr *EnvMgr) NewDefExistProp_InsideAtomsDeclared(stmt *ast.DefExistPropStmt) ast.StmtRet{
// 	// prop名不能和parameter名重叠
// 	if slices.Contains(append(stmt.ExistParams, stmt.DefBody.DefHeader.Params...), string(stmt.DefBody.DefHeader.Name)) {
// 		return ast.StmtErrRet(fmt.Sprintf("prop name %s cannot be the same as parameter name %s", stmt.DefBody.DefHeader.Name, stmt.DefBody.DefHeader.Name))
// 	}

// 	extraAtomNames := map[string]struct{}{}
// 	for _, param := range stmt.DefBody.DefHeader.Params {
// 		extraAtomNames[param] = struct{}{}
// 	}
// 	extraAtomNames[string(stmt.DefBody.DefHeader.Name)] = struct{}{}

// 	for _, param := range stmt.ExistParams {
// 		extraAtomNames[param] = struct{}{}
// 	}

// 	for _, fact := range stmt.DefBody.DomFactsOrNil {
// 		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
// 		if ret.IsErr() {
// 			ret.AddError(fmt.Sprintf("in dom fact of exist_prop %s definition", stmt.DefBody.DefHeader.Name))
// 			return ret
// 		}
// 	}

// 	for _, fact := range stmt.DefBody.IffFactsOrNil {
// 		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
// 		if ret.IsErr() {
// 			ret.AddError(fmt.Sprintf("in iff fact of exist_prop %s definition", stmt.DefBody.DefHeader.Name))
// 			return ret
// 		}
// 	}

// 	ret := envMgr.IsValidAndAvailableName(string(stmt.DefBody.DefHeader.Name))
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	key := string(stmt.DefBody.DefHeader.Name)

// 	// Save to AllDefinedExistPropNames
// 	envMgr.AllDefinedExistPropNames[key] = stmt

// 	// Mark in current EnvSlice
// 	envMgr.CurEnv().ExistPropDefMem[key] = struct{}{}

// 	return glob.NewEmptyStmtTrue()
// }

func (envMgr *EnvMgr) CheckAtomObjNameIsValidAndAvailableThenDefineIt(name string) (bool, string) {
	ret := envMgr.IsValidAndAvailableName(name)
	if !ret {
		return false, fmt.Sprintf("invalid name: %s", name)
	}

	// Save to AllDefinedAtomObjNames
	envMgr.AllDefinedAtomObjNames[name] = NewDefinedStuff(struct{}{}, envMgr.CurEnvDepth())

	// Mark in current EnvSlice
	envMgr.CurEnv().AtomObjDefMem[name] = struct{}{}

	return true, ""
}

func (envMgr *EnvMgr) StoreFnIsAFn(fnName ast.Obj, fnSet *ast.FnSetObj) (bool, string) {
	ret := envMgr.IsValidAndAvailableName(fnName.String())
	if !ret {
		return false, fmt.Sprintf("invalid name: %s", fnName)
	}

	envMgr.AllDefinedFns[fnName.String()] = NewDefinedStuff(fnSet, envMgr.CurEnvDepth())
	envMgr.CurEnv().FnDefMem[fnName.String()] = struct{}{}

	return true, ""
}

// DefLetStmt defines new objects in the environment
// and checks that all atoms inside the facts are declared.
// If the obj is a function, it will be inserted into the function definition memory.
func (envMgr *EnvMgr) DefLetStmt(stmt *ast.DefLetStmt) ast.StmtRet {
	implyMsgs := []ast.InferRet{}
	// If this obj is a function, it will be inserted into the function definition memory
	for _, objName := range stmt.Objs {
		ok, msg := envMgr.CheckAtomObjNameIsValidAndAvailableThenDefineIt(objName)
		if !ok {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(msg)
		}
	}

	for _, fact := range stmt.NewInFacts() {
		ret := envMgr.LookUpNamesInFact(fact, map[string]struct{}{})
		if ret.IsErr() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo("in new in fact of def let statement")
		}
		ret2 := envMgr.NewFactWithCheckingNameDefined(fact)
		if ret2.IsErr() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo("in new fact with checking name defined of def let statement")
		}
		implyMsgs = append(implyMsgs)
	}

	for _, fact := range stmt.Facts {
		ret := envMgr.LookUpNamesInFact(fact, map[string]struct{}{})
		if ret.IsNotTrue() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo("in fact of def let statement")
		}
		ret2 := envMgr.NewFactWithCheckingNameDefined(fact)
		if ret2.IsNotTrue() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo("in new fact with checking name defined of def let statement")
		}
		implyMsgs = append(implyMsgs, ret2)
	}

	return ast.NewTrueStmtEmptyRet(stmt).AddInfers(implyMsgs)
}
