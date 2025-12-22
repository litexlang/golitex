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
	"slices"
)

func (envMgr *EnvMgr) curEnvDepth() int {
	return len(envMgr.EnvSlice) - 1
}

func (envMgr *EnvMgr) CurEnv() *EnvMemory {
	return &envMgr.EnvSlice[len(envMgr.EnvSlice)-1]
}

func (envMgr *EnvMgr) NewDefProp_BuiltinProp(stmt *ast.DefPropStmt) glob.GlobRet {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, string(stmt.DefHeader.Name)) {
		return glob.ErrRet(fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name))
	}

	ret := envMgr.IsValidIdentifierAvailable(string(stmt.DefHeader.Name))
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) NewDefProp_InsideAtomsDeclared(stmt *ast.DefPropStmt) glob.GlobRet {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, string(stmt.DefHeader.Name)) {
		return glob.ErrRet(fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name))
	}

	ret := envMgr.IsValidIdentifierAvailable(string(stmt.DefHeader.Name))
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefHeader.Name)] = struct{}{}

	for _, fact := range stmt.DomFactsOrNil {
		ret := envMgr.AtomObjsInFactProperlyDefined(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in dom fact of prop %s definition", stmt.DefHeader.Name))
			return ret
		}
	}

	for _, fact := range stmt.IffFactsOrNil {
		ret := envMgr.AtomObjsInFactProperlyDefined(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in iff fact of prop %s definition", stmt.DefHeader.Name))
			return ret
		}
	}

	key := string(stmt.DefHeader.Name)

	// Save to AllDefinedPropNames
	envMgr.AllDefinedPropNames[key] = stmt

	// Mark in current EnvSlice
	envMgr.CurEnv().PropDefMem[key] = struct{}{}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) AtomsInFnTemplateFnTemplateDeclared(name ast.Atom, stmt *ast.DefFnSetStmt) glob.GlobRet {
	// fn名不能和parameter名重叠
	if slices.Contains(stmt.TemplateDefHeader.Params, string(name)) {
		return glob.ErrRet(fmt.Errorf("fn name %s cannot be the same as parameter name %s", name, name))
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.TemplateDefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}

	ret := envMgr.AtomsInObjDefinedOrBuiltin(stmt.Fn.RetSet, extraAtomNames)
	if ret.IsErr() {
		ret.AddMsg(fmt.Sprintf("in return set of fn template %s", name))
		return ret
	}

	extraAtomNames[string(name)] = struct{}{}

	for _, fact := range stmt.TemplateDomFacts {
		ret := envMgr.AtomObjsInFactProperlyDefined(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in template dom fact of fn %s definition", name))
			return ret
		}
	}

	// ret = envMgr.NonDuplicateParam_NoUndeclaredParamSet_ExtraAtomNames(stmt.Fn.Params, stmt.Fn.ParamSets, extraAtomNames, false)
	// if ret.IsErr() {
	// 	return ret
	// }

	for _, param := range stmt.Fn.Params {
		extraAtomNames[param] = struct{}{}
	}

	for _, fact := range stmt.Fn.DomFacts {
		ret := envMgr.AtomObjsInFactProperlyDefined(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in dom fact of fn %s definition", name))
			return ret
		}
	}

	for _, fact := range stmt.Fn.ThenFacts {
		ret := envMgr.AtomObjsInFactProperlyDefined(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in then fact of fn %s definition", name))
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) NewDefExistProp_InsideAtomsDeclared(stmt *ast.DefExistPropStmt) glob.GlobRet {
	// prop名不能和parameter名重叠
	if slices.Contains(append(stmt.ExistParams, stmt.DefBody.DefHeader.Params...), string(stmt.DefBody.DefHeader.Name)) {
		return glob.ErrRet(fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefBody.DefHeader.Name, stmt.DefBody.DefHeader.Name))
	}

	// ret := envMgr.NoDuplicateParamNamesAndParamSetsDefined(append(stmt.DefBody.DefHeader.Params, stmt.ExistParams...), append(stmt.DefBody.DefHeader.ParamSets, stmt.ExistParamSets...), true)
	// if ret.IsErr() {
	// 	return ret
	// }

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefBody.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefBody.DefHeader.Name)] = struct{}{}

	for _, param := range stmt.ExistParams {
		extraAtomNames[param] = struct{}{}
	}

	for _, fact := range stmt.DefBody.DomFactsOrNil {
		ret := envMgr.AtomObjsInFactProperlyDefined(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in dom fact of exist_prop %s definition", stmt.DefBody.DefHeader.Name))
			return ret
		}
	}

	for _, fact := range stmt.DefBody.IffFactsOrNil {
		ret := envMgr.AtomObjsInFactProperlyDefined(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in iff fact of exist_prop %s definition", stmt.DefBody.DefHeader.Name))
			return ret
		}
	}

	ret := envMgr.IsValidIdentifierAvailable(string(stmt.DefBody.DefHeader.Name))
	if ret.IsErr() {
		return ret
	}

	key := string(stmt.DefBody.DefHeader.Name)

	// Save to AllDefinedExistPropNames
	envMgr.AllDefinedExistPropNames[key] = stmt

	// Mark in current EnvSlice
	envMgr.CurEnv().ExistPropDefMem[key] = struct{}{}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) NewObj_NoDuplicate(name string, stmt *ast.DefLetStmt) glob.GlobRet {
	ret := envMgr.IsValidIdentifierAvailable(name)
	if ret.IsErr() {
		return glob.ErrRet(fmt.Errorf("invalid name: %s", name))
	}

	// Save to AllDefinedAtomObjNames
	envMgr.AllDefinedAtomObjNames[name] = stmt

	// Mark in current EnvSlice
	envMgr.CurEnv().AtomObjDefMem[name] = struct{}{}

	return glob.NewEmptyGlobTrue()
}

// DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined defines new objects in the environment
// and checks that all atoms inside the facts are declared.
// If the obj is a function, it will be inserted into the function definition memory.
func (envMgr *EnvMgr) DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(stmt *ast.DefLetStmt) glob.GlobRet {
	// ret := envMgr.NoDuplicateParamNamesAndParamSetsDefined(stmt.Objs, stmt.ObjSets, true)
	// if ret.IsErr() {
	// 	return ret
	// }

	extraAtomNames := map[string]struct{}{}

	for _, objName := range stmt.Objs {
		ret := envMgr.IsValidIdentifierAvailable(objName)
		if ret.IsErr() {
			return ret
		}
	}

	// If this obj is a function, it will be inserted into the function definition memory
	for _, objName := range stmt.Objs {
		ret := envMgr.NewObj_NoDuplicate(objName, stmt)
		if ret.IsErr() {
			return ret
		}
	}

	for _, fact := range stmt.NewInFacts() {
		ret := envMgr.AtomObjsInFactProperlyDefined(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg("in new in fact of def let statement")
			return ret
		}
		ret = envMgr.NewFactWithAtomsDefined(fact)
		if ret.IsErr() {
			return ret
		}
	}

	implicationFacts := []string{}
	for _, fact := range stmt.Facts {
		ret := envMgr.AtomObjsInFactProperlyDefined(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg("in fact of def let statement")
			return ret
		}
		ret = envMgr.NewFactWithAtomsDefined(fact)
		if ret.IsErr() {
			return ret
		}
		if ret.IsTrue() {
			implicationFacts = append(implicationFacts, ret.String())
		}
	}

	return glob.NewGlobTrueWithMsgs(implicationFacts)
}
