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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"slices"
)

func (env *Env) IsValidUserDefinedName_NoDuplicate(name string) error {
	err := glob.IsValidUseDefinedFcAtom(name)
	if err != nil {
		return err
	}

	ok := env.IsFcAtomDeclaredByUser(ast.FcAtom(name))
	if ok {
		return duplicateDefError(glob.EmptyPkg, name, "")
	}

	// 不清楚是否允许pkg name 和 obj name 重叠，目前允许

	return nil
}

func (env *Env) NewDefProp_InsideAtomsDeclared(stmt *ast.DefPropStmt) error {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, stmt.DefHeader.Name) {
		return fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name)
	}

	err := env.IsValidUserDefinedName_NoDuplicate(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	err = env.NonDuplicateParam_NoUndeclaredParamSet(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, true)
	if err != nil {
		return err
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[stmt.DefHeader.Name] = struct{}{}

	for _, fact := range stmt.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf("%v\nis true by prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefHeader.Name)
		}
	}

	for _, fact := range stmt.IffFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf("%v\nis true by prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefHeader.Name)
		}
	}

	key := stmt.DefHeader.Name
	env.PropDefMem[key] = *stmt
	return nil
}

func (env *Env) AtomsInFnTemplateDeclared(nameAsFc ast.Fc, stmt *ast.FnTemplateStmt) error {
	// fn名不能和parameter名重叠
	name := nameAsFc.String()

	if slices.Contains(stmt.Params, name) {
		return fmt.Errorf("fn name %s cannot be the same as parameter name %s", name, name)
	}

	err := env.NonDuplicateParam_NoUndeclaredParamSet(stmt.Params, stmt.ParamSets, false)
	if err != nil {
		return err
	}
	ok := env.AreAtomsInFcAreDeclared(stmt.RetSet, map[string]struct{}{})
	if !ok {
		return fmt.Errorf(AtomsInFcNotDeclaredMsg(stmt.RetSet))
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[name] = struct{}{}

	for _, fact := range stmt.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf("%v\nis true by fn %s definition, but there are undeclared atoms in the fact", fact, name)
		}
	}

	for _, fact := range stmt.ThenFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf("%v\nis true by fn %s definition, but there are undeclared atoms in the fact", fact, name)
		}
	}

	// TODO: WARNING: 这里有严重问题。因为貌似同一个fn可以implement很多的fn_template，所以即使之前知道它怎么样，我也不能说明什么问题
	// err = env.IsValidUserDefinedName_NoDuplicate(stmt.DefHeader.Name)
	// if err != nil {
	// 	return err
	// }

	return nil
}

func (env *Env) NewDefExistProp_InsideAtomsDeclared(stmt *ast.DefExistPropStmt) error {
	// prop名不能和parameter名重叠
	if slices.Contains(append(stmt.ExistParams, stmt.DefBody.DefHeader.Params...), stmt.DefBody.DefHeader.Name) {
		return fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefBody.DefHeader.Name, stmt.DefBody.DefHeader.Name)
	}

	err := env.NonDuplicateParam_NoUndeclaredParamSet(append(stmt.DefBody.DefHeader.Params, stmt.ExistParams...), append(stmt.DefBody.DefHeader.ParamSets, stmt.ExistParamSets...), true)
	if err != nil {
		return err
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefBody.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[stmt.DefBody.DefHeader.Name] = struct{}{}

	for _, param := range stmt.ExistParams {
		extraAtomNames[param] = struct{}{}
	}

	for _, fact := range stmt.DefBody.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf("%v\nis true by exist_prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefBody.DefHeader.Name)
		}
	}

	for _, fact := range stmt.DefBody.IffFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf("%v\nis true by exist_prop %s definition, but there are undeclared atoms in the fact", fact, stmt.DefBody.DefHeader.Name)
		}
	}

	err = env.IsValidUserDefinedName_NoDuplicate(stmt.DefBody.DefHeader.Name)
	if err != nil {
		return err
	}

	key := stmt.DefBody.DefHeader.Name
	env.ExistPropDefMem[key] = *stmt
	return nil
}

func (e *Env) NewObj_NoDuplicate(name string, stmt ast.FnTemplate_Or_DefObjStmtInterface) error {
	err := e.IsValidUserDefinedName_NoDuplicate(name)
	if err != nil {
		return fmt.Errorf("invalid name: %s", name)
	}

	e.ObjDefMem[name] = stmt

	return nil
}
