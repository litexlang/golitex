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

func (env *Env) IsValidIdentifierAvailable(name string) glob.GlobRet {
	err := glob.IsValidUseDefinedFcAtom(name)
	if err != nil {
		return glob.ErrRet(err)
	}

	ok := env.IsFcAtomDeclaredByUser(ast.AtomObj(name))
	if ok {
		return glob.ErrRet(duplicateDefError(name))
	}

	return glob.TrueRet("")
}

func (env *Env) NewDefProp_BuiltinProp(stmt *ast.DefPropStmt) glob.GlobRet {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, string(stmt.DefHeader.Name)) {
		return glob.ErrRet(fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name))
	}

	ret := env.ThereIsNoDuplicateObjNamesAndAllAtomsInParamSetsAreDefined(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, true)
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefHeader.Name)] = struct{}{}

	for _, fact := range stmt.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf("%s\nis true by prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefHeader.Name))
		}
	}

	for _, fact := range stmt.IffFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf("%s\nis true by prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefHeader.Name))
		}
	}

	key := string(stmt.DefHeader.Name)
	env.PropDefMem[key] = *stmt
	return glob.TrueRet("")
}

func (env *Env) NewDefProp_InsideAtomsDeclared(stmt *ast.DefPropStmt) glob.GlobRet {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, string(stmt.DefHeader.Name)) {
		return glob.ErrRet(fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name))
	}

	ret := env.IsValidIdentifierAvailable(string(stmt.DefHeader.Name))
	if ret.IsErr() {
		return ret
	}

	ret = env.ThereIsNoDuplicateObjNamesAndAllAtomsInParamSetsAreDefined(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, true)
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefHeader.Name)] = struct{}{}

	for _, fact := range stmt.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf("%s\nis true by prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefHeader.Name))
		}
	}

	for _, fact := range stmt.IffFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf("%s\nis true by prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefHeader.Name))
		}
	}

	key := string(stmt.DefHeader.Name)
	env.PropDefMem[key] = *stmt
	return glob.TrueRet("")
}

func (env *Env) AtomsInFnTemplateFnTemplateDeclared(name ast.AtomObj, stmt *ast.FnTemplateDefStmt) glob.GlobRet {
	// fn名不能和parameter名重叠
	if slices.Contains(stmt.TemplateDefHeader.Params, string(name)) {
		return glob.ErrRet(fmt.Errorf("fn name %s cannot be the same as parameter name %s", name, name))
	}

	ret := env.ThereIsNoDuplicateObjNamesAndAllAtomsInParamSetsAreDefined(stmt.TemplateDefHeader.Params, stmt.TemplateDefHeader.ParamSets, false)
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.TemplateDefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}

	ok := env.AreAtomsInFcAreDeclared(stmt.Fn.RetSet, extraAtomNames)
	if !ok {
		return glob.ErrRet(fmt.Errorf(AtomsInFcNotDeclaredMsg(stmt.Fn.RetSet)))
	}

	extraAtomNames[string(name)] = struct{}{}

	for _, fact := range stmt.TemplateDomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf("%s\nis true by fn %s definition, but there are undeclared atoms in the fact", fact, name))
		}
	}

	ret = env.NonDuplicateParam_NoUndeclaredParamSet_ExtraAtomNames(stmt.Fn.Params, stmt.Fn.ParamSets, extraAtomNames, false)
	if ret.IsErr() {
		return ret
	}

	for _, param := range stmt.Fn.Params {
		extraAtomNames[param] = struct{}{}
	}

	for _, fact := range stmt.Fn.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf("%s\nis true by fn %s definition, but there are undeclared atoms in the fact", fact, name))
		}
	}

	for _, fact := range stmt.Fn.ThenFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf("%s\nis true by fn %s definition, but there are undeclared atoms in the fact", fact, name))
		}
	}

	return glob.TrueRet("")
}

func (env *Env) NewDefExistProp_InsideAtomsDeclared(stmt *ast.DefExistPropStmt) glob.GlobRet {
	// prop名不能和parameter名重叠
	if slices.Contains(append(stmt.ExistParams, stmt.DefBody.DefHeader.Params...), string(stmt.DefBody.DefHeader.Name)) {
		return glob.ErrRet(fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefBody.DefHeader.Name, stmt.DefBody.DefHeader.Name))
	}

	ret := env.ThereIsNoDuplicateObjNamesAndAllAtomsInParamSetsAreDefined(append(stmt.DefBody.DefHeader.Params, stmt.ExistParams...), append(stmt.DefBody.DefHeader.ParamSets, stmt.ExistParamSets...), true)
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefBody.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefBody.DefHeader.Name)] = struct{}{}

	for _, param := range stmt.ExistParams {
		extraAtomNames[param] = struct{}{}
	}

	for _, fact := range stmt.DefBody.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf("%s\nis true by exist_prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefBody.DefHeader.Name))
		}
	}

	for _, fact := range stmt.DefBody.IffFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf("%s\nis true by exist_prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefBody.DefHeader.Name))
		}
	}

	ret = env.IsValidIdentifierAvailable(string(stmt.DefBody.DefHeader.Name))
	if ret.IsErr() {
		return ret
	}

	key := string(stmt.DefBody.DefHeader.Name)
	env.ExistPropDefMem[key] = *stmt
	return glob.TrueRet("")
}

func (e *Env) NewObj_NoDuplicate(name string, stmt ast.FnTemplate_Or_DefObjStmtInterface) glob.GlobRet {
	ret := e.IsValidIdentifierAvailable(name)
	if ret.IsErr() {
		return glob.ErrRet(fmt.Errorf("invalid name: %s", name))
	}

	e.ObjDefMem[name] = stmt

	return glob.TrueRet("")
}

// DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined defines new objects in the environment
// and checks that all atoms inside the facts are declared.
// If the obj is a function, it will be inserted into the function definition memory.
func (env *Env) DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(stmt *ast.DefLetStmt) glob.GlobRet {
	ret := env.ThereIsNoDuplicateObjNamesAndAllAtomsInParamSetsAreDefined(stmt.Objs, stmt.ObjSets, true)
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}

	for _, objName := range stmt.Objs {
		ret := env.IsValidIdentifierAvailable(objName)
		if ret.IsErr() {
			return ret
		}
	}

	// If this obj is a function, it will be inserted into the function definition memory
	for _, objName := range stmt.Objs {
		ret = env.NewObj_NoDuplicate(objName, stmt)
		if ret.IsErr() {
			return ret
		}
	}

	for _, fact := range stmt.NewInFacts() {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf(AtomsInFactNotDeclaredMsg(fact)))
		}
		ret := env.NewFact(fact)
		if ret.IsErr() {
			return ret
		}
	}

	for _, fact := range stmt.Facts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return glob.ErrRet(fmt.Errorf(AtomsInFactNotDeclaredMsg(fact)))
		}
		ret := env.NewFact(fact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.TrueRet("")
}
