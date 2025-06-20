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
// Litex Zulip community: https://litex.zulipchat.com

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"slices"
)

func (env *Env) IsInvalidName(name string) error {
	err := glob.IsValidName(name)
	if err != nil {
		return err
	}

	for curEnv := env; curEnv != nil; curEnv = curEnv.Parent {
		_, ok := curEnv.ObjDefMem.Dict[glob.EmptyPkg][name]
		if ok {
			return duplicateDefMsg(glob.EmptyPkg, name, glob.KeywordObj)
		}
		_, ok = curEnv.FnDefMem.Dict[glob.EmptyPkg][name]
		if ok {
			return duplicateDefMsg(glob.EmptyPkg, name, glob.KeywordFn)
		}
		_, ok = curEnv.PropDefMem.Dict[glob.EmptyPkg][name]
		if ok {
			return duplicateDefMsg(glob.EmptyPkg, name, glob.KeywordProp)
		}
		_, ok = curEnv.ExistPropDefMem.Dict[glob.EmptyPkg][name]
		if ok {
			return duplicateDefMsg(glob.EmptyPkg, name, glob.KeywordExistProp)
		}
	}

	return nil
}

// func (env *Env) isDeclaredFn_Prop_ExistProp(name string) bool {
// 	for curEnv := env; curEnv != nil; curEnv = curEnv.Parent {
// 		_, ok := curEnv.FnDefMem.Dict[glob.EmptyPkg][name]
// 		if ok {
// 			return true
// 		}
// 		_, ok = curEnv.PropDefMem.Dict[glob.EmptyPkg][name]
// 		if ok {
// 			return true
// 		}
// 		_, ok = curEnv.ExistPropDefMem.Dict[glob.EmptyPkg][name]
// 		if ok {
// 			return true
// 		}
// 	}
// 	return false
// }

func (env *Env) NewDefProp_InsideAtomsDeclared(stmt *ast.DefPropStmt) error {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, stmt.DefHeader.Name) {
		return fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name)
	}

	err := env.IsInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	err = env.NonDuplicateParam_NoUndeclaredParamSet(stmt.DefHeader.Params, stmt.DefHeader.SetParams, true)
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
			return fmt.Errorf(fmt.Sprintf("%s\nis true by prop %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefHeader.Name))
		}
	}

	for _, fact := range stmt.IffFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf(fmt.Sprintf("%s\nis true by prop %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefHeader.Name))
		}
	}

	return env.PropDefMem.insert(stmt, glob.EmptyPkg)
}

// func (env *Env) NewDefObj_InsideAtomsDeclared(stmt *ast.DefObjStmt) error {
// 	err := env.NonDuplicateParam_NoUndeclaredParamSet(stmt.Objs, stmt.ObjSets, true)
// 	if err != nil {
// 		return err
// 	}

// 	extraAtomNames := map[string]struct{}{}
// 	for _, objName := range stmt.Objs {
// 		extraAtomNames[objName] = struct{}{}
// 	}

// 	for _, fact := range stmt.NewInFacts() {
// 		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
// 			return fmt.Errorf(AtomsInFactNotDeclaredMsg(fact))
// 		}
// 		err := env.NewFact(fact)
// 		if err != nil {
// 			return err
// 		}
// 	}

// 	for _, fact := range stmt.Facts {
// 		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
// 			return fmt.Errorf(AtomsInFactNotDeclaredMsg(fact))
// 		}
// 		err := env.NewFact(fact)
// 		if err != nil {
// 			return err
// 		}
// 	}

// 	for _, objName := range stmt.Objs {
// 		err := env.IsInvalidName(objName)
// 		if err != nil {
// 			return err
// 		}
// 	}

// 	// 如果这个obj是fn，那么要插入到fn def mem中
// 	for i, objName := range stmt.Objs {
// 		if ast.IsFnDeclarationFc(stmt.ObjSets[i]) {
// 			fnDefStmt := ast.FromFnDeclFcToDefFnStmt(objName, stmt.ObjSets[i])
// 			err = env.NewDefFn_InsideAtomsDeclared(fnDefStmt)
// 			if err != nil {
// 				return err
// 			}
// 		} else {
// 			err = env.ObjDefMem.InsertItem(objName)
// 			if err != nil {
// 				return err
// 			}
// 		}
// 	}

// 	return nil
// }

func (env *Env) NewDefFn_InsideAtomsDeclared(stmt *ast.DefFnStmt) error {
	// fn名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, stmt.DefHeader.Name) {
		return fmt.Errorf("fn name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name)
	}

	err := env.NonDuplicateParam_NoUndeclaredParamSet(stmt.DefHeader.Params, stmt.DefHeader.SetParams, false)
	if err != nil {
		return err
	}
	ok := env.AreAtomsInFcAreDeclared(stmt.RetSet, map[string]struct{}{})
	if !ok {
		return fmt.Errorf(AtomsInFcNotDeclaredMsg(stmt.RetSet))
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}
	extraAtomNames[stmt.DefHeader.Name] = struct{}{}

	for _, fact := range stmt.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf(fmt.Sprintf("%s\nis true by fn %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefHeader.Name))
		}
	}

	for _, fact := range stmt.ThenFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf(fmt.Sprintf("%s\nis true by fn %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefHeader.Name))
		}
	}

	// TODO: WARNING: 这里有严重问题。因为貌似同一个fn可以implement很多的fn_template，所以即使之前知道它怎么样，我也不能说明什么问题
	err = env.IsInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	err = env.FnDefMem.insert(stmt, glob.EmptyPkg)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) NewDefExistProp_InsideAtomsDeclared(stmt *ast.DefExistPropStmt) error {
	// prop名不能和parameter名重叠
	if slices.Contains(append(stmt.ExistParams, stmt.DefBody.DefHeader.Params...), stmt.DefBody.DefHeader.Name) {
		return fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefBody.DefHeader.Name, stmt.DefBody.DefHeader.Name)
	}

	err := env.NonDuplicateParam_NoUndeclaredParamSet(append(stmt.DefBody.DefHeader.Params, stmt.ExistParams...), append(stmt.DefBody.DefHeader.SetParams, stmt.ExistParamSets...), true)
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
			return fmt.Errorf(fmt.Sprintf("%s\nis true by exist_prop %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefBody.DefHeader.Name))
		}
	}

	for _, fact := range stmt.DefBody.IffFacts {
		if !env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf(fmt.Sprintf("%s\nis true by exist_prop %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefBody.DefHeader.Name))
		}
	}

	err = env.IsInvalidName(stmt.DefBody.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.ExistPropDefMem.insert(stmt, glob.EmptyPkg)
}
