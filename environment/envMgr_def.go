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
	"slices"
)

func (envMgr *EnvMgr) NewDefProp_InsideAtomsDeclared(stmt *ast.DefPropStmt) *glob.StmtRet {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, string(stmt.DefHeader.Name)) {
		return glob.ErrRet(fmt.Sprintf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name))
	}

	ret := envMgr.IsValidAndAvailableName(string(stmt.DefHeader.Name))
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefHeader.Name)] = struct{}{}

	for _, fact := range stmt.DomFactsOrNil {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddError(fmt.Sprintf("in dom fact of prop %s definition", stmt.DefHeader.Name))
			return ret
		}
	}

	for _, fact := range stmt.IffFactsOrNil {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddError(fmt.Sprintf("in iff fact of prop %s definition", stmt.DefHeader.Name))
			return ret
		}
	}

	key := string(stmt.DefHeader.Name)

	// Save to AllDefinedPropNames
	envMgr.AllDefinedPropNames[key] = stmt

	// Mark in current EnvSlice
	envMgr.CurEnv().PropDefMem[key] = struct{}{}

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) AtomsInFnTemplateFnTemplateDeclared(name ast.Atom, stmt *ast.DefFnSetStmt) *glob.StmtRet {
	// fn名不能和parameter名重叠
	if slices.Contains(stmt.TemplateDefHeader.Params, string(name)) {
		return glob.ErrRet(fmt.Sprintf("fn name %s cannot be the same as parameter name %s", name, name))
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.TemplateDefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}

	ret := envMgr.LookupNamesInObj(stmt.AnonymousFn.RetSet, extraAtomNames)
	if ret.IsErr() {
		ret.AddError(fmt.Sprintf("in return set of fn template %s", name))
		return ret
	}

	extraAtomNames[string(name)] = struct{}{}

	for _, fact := range stmt.TemplateDomFacts {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddError(fmt.Sprintf("in template dom fact of fn %s definition", name))
			return ret
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
			ret.AddError(fmt.Sprintf("in dom fact of fn %s definition", name))
			return ret
		}
	}

	for _, fact := range stmt.AnonymousFn.ThenFacts {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddError(fmt.Sprintf("in then fact of fn %s definition", name))
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) NewDefExistProp_InsideAtomsDeclared(stmt *ast.DefExistPropStmt) *glob.StmtRet {
	// prop名不能和parameter名重叠
	if slices.Contains(append(stmt.ExistParams, stmt.DefBody.DefHeader.Params...), string(stmt.DefBody.DefHeader.Name)) {
		return glob.ErrRet(fmt.Sprintf("prop name %s cannot be the same as parameter name %s", stmt.DefBody.DefHeader.Name, stmt.DefBody.DefHeader.Name))
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefBody.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefBody.DefHeader.Name)] = struct{}{}

	for _, param := range stmt.ExistParams {
		extraAtomNames[param] = struct{}{}
	}

	for _, fact := range stmt.DefBody.DomFactsOrNil {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddError(fmt.Sprintf("in dom fact of exist_prop %s definition", stmt.DefBody.DefHeader.Name))
			return ret
		}
	}

	for _, fact := range stmt.DefBody.IffFactsOrNil {
		ret := envMgr.LookUpNamesInFact(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddError(fmt.Sprintf("in iff fact of exist_prop %s definition", stmt.DefBody.DefHeader.Name))
			return ret
		}
	}

	ret := envMgr.IsValidAndAvailableName(string(stmt.DefBody.DefHeader.Name))
	if ret.IsErr() {
		return ret
	}

	key := string(stmt.DefBody.DefHeader.Name)

	// Save to AllDefinedExistPropNames
	envMgr.AllDefinedExistPropNames[key] = stmt

	// Mark in current EnvSlice
	envMgr.CurEnv().ExistPropDefMem[key] = struct{}{}

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) CheckAtomObjNameIsValidAndAvailableThenDefineIt(name string) *glob.StmtRet {
	ret := envMgr.IsValidAndAvailableName(name)
	if ret.IsErr() {
		return glob.ErrRet(fmt.Sprintf("invalid name: %s", name))
	}

	// Save to AllDefinedAtomObjNames
	envMgr.AllDefinedAtomObjNames[name] = struct{}{}

	// Mark in current EnvSlice
	envMgr.CurEnv().AtomObjDefMem[name] = struct{}{}

	return glob.NewEmptyStmtTrue()
}

// DefLetStmt defines new objects in the environment
// and checks that all atoms inside the facts are declared.
// If the obj is a function, it will be inserted into the function definition memory.
func (envMgr *EnvMgr) DefLetStmt(stmt *ast.DefLetStmt) *glob.StmtRet {
	implyMsgs := []string{}
	defineFacts := []string{}
	// If this obj is a function, it will be inserted into the function definition memory
	for _, objName := range stmt.Objs {
		ret := envMgr.CheckAtomObjNameIsValidAndAvailableThenDefineIt(objName)
		if ret.IsErr() {
			return ret
		}
		defineFacts = append(defineFacts, glob.IsANewObjectMsg(objName))
	}

	for _, fact := range stmt.NewInFacts() {
		ret := envMgr.LookUpNamesInFact(fact, map[string]struct{}{})
		if ret.IsErr() {
			ret.AddError("in new in fact of def let statement")
			return ret
		}
		ret = envMgr.NewFactWithoutCheckingNameDefined(fact)
		if ret.IsErr() {
			return ret
		}
		defineFacts = append(defineFacts, fact.String())
		implyMsgs = append(implyMsgs, ret.Infer...)
	}

	for _, fact := range stmt.Facts {
		ret := envMgr.LookUpNamesInFact(fact, map[string]struct{}{})
		if ret.IsErr() {
			ret.AddError("in fact of def let statement")
			return ret
		}
		ret = envMgr.NewFactWithoutCheckingNameDefined(fact)
		if ret.IsErr() {
			return ret
		}
		if ret.IsTrue() {
			defineFacts = append(defineFacts, fact.String())
		}
		implyMsgs = append(implyMsgs, ret.Infer...)
	}

	return glob.NewStmtTrueRetWithDefines(defineFacts).AddInfers(implyMsgs)
}
