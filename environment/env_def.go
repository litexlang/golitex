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
	err := glob.IsValidUseDefinedAtomObj(name)
	if err != nil {
		return glob.ErrRet(err)
	}

	ret := env.IsAtomDefinedByUser(ast.Atom(name))
	if ret.IsTrue() {
		return glob.ErrRet(duplicateDefError(name))
	}

	return glob.TrueRet("")
}

func (env *Env) NewDefProp_BuiltinProp(stmt *ast.DefPropStmt) glob.GlobRet {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, string(stmt.DefHeader.Name)) {
		return glob.ErrRet(fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name))
	}

	ret := env.NoDuplicateParamNamesAndParamSetsDefined(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, true)
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefHeader.Name)] = struct{}{}

	for _, fact := range stmt.DomFacts {
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in dom fact of prop %s definition", stmt.DefHeader.Name))
			return ret
		}
	}

	for _, fact := range stmt.IffFacts {
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in iff fact of prop %s definition", stmt.DefHeader.Name))
			return ret
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

	ret = env.NoDuplicateParamNamesAndParamSetsDefined(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, true)
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[string(stmt.DefHeader.Name)] = struct{}{}

	for _, fact := range stmt.DomFacts {
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in dom fact of prop %s definition", stmt.DefHeader.Name))
			return ret
		}
	}

	for _, fact := range stmt.IffFacts {
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in iff fact of prop %s definition", stmt.DefHeader.Name))
			return ret
		}
	}

	key := string(stmt.DefHeader.Name)
	env.PropDefMem[key] = *stmt
	return glob.TrueRet("")
}

func (env *Env) AtomsInFnTemplateFnTemplateDeclared(name ast.Atom, stmt *ast.FnTemplateDefStmt) glob.GlobRet {
	// fn名不能和parameter名重叠
	if slices.Contains(stmt.TemplateDefHeader.Params, string(name)) {
		return glob.ErrRet(fmt.Errorf("fn name %s cannot be the same as parameter name %s", name, name))
	}

	ret := env.NoDuplicateParamNamesAndParamSetsDefined(stmt.TemplateDefHeader.Params, stmt.TemplateDefHeader.ParamSets, false)
	if ret.IsErr() {
		return ret
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.TemplateDefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}

	ret = env.AreAtomsInObjDefined(stmt.Fn.RetSet, extraAtomNames)
	if ret.IsErr() {
		ret.AddMsg(fmt.Sprintf("in return set of fn template %s", name))
		return ret
	}

	extraAtomNames[string(name)] = struct{}{}

	for _, fact := range stmt.TemplateDomFacts {
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in template dom fact of fn %s definition", name))
			return ret
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
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in dom fact of fn %s definition", name))
			return ret
		}
	}

	for _, fact := range stmt.Fn.ThenFacts {
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in then fact of fn %s definition", name))
			return ret
		}
	}

	return glob.TrueRet("")
}

func (env *Env) NewDefExistProp_InsideAtomsDeclared(stmt *ast.DefExistPropStmt) glob.GlobRet {
	// prop名不能和parameter名重叠
	if slices.Contains(append(stmt.ExistParams, stmt.DefBody.DefHeader.Params...), string(stmt.DefBody.DefHeader.Name)) {
		return glob.ErrRet(fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefBody.DefHeader.Name, stmt.DefBody.DefHeader.Name))
	}

	ret := env.NoDuplicateParamNamesAndParamSetsDefined(append(stmt.DefBody.DefHeader.Params, stmt.ExistParams...), append(stmt.DefBody.DefHeader.ParamSets, stmt.ExistParamSets...), true)
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
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in dom fact of exist_prop %s definition", stmt.DefBody.DefHeader.Name))
			return ret
		}
	}

	for _, fact := range stmt.DefBody.IffFacts {
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in iff fact of exist_prop %s definition", stmt.DefBody.DefHeader.Name))
			return ret
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
	ret := env.NoDuplicateParamNamesAndParamSetsDefined(stmt.Objs, stmt.ObjSets, true)
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
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg("in new in fact of def let statement")
			return ret
		}
		ret = env.NewFact(fact)
		if ret.IsErr() {
			return ret
		}
	}

	for _, fact := range stmt.Facts {
		ret := env.AreAtomsInFactAreDeclared(fact, extraAtomNames)
		if ret.IsErr() {
			ret.AddMsg("in fact of def let statement")
			return ret
		}
		ret = env.NewFact(fact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.TrueRet("")
}
