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
)

func (env *Env) isInvalidName(name string) error {
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
	}

	return nil
}

func (env *Env) NewDefProp_InsideAtomsDeclared(stmt *ast.DefPropStmt) error {
	err := env.isInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	err = env.NonDuplicateParam_NoUndeclaredParamSet(stmt.DefHeader.Params, stmt.DefHeader.SetParams)
	if err != nil {
		return err
	}

	extraAtomNames := map[string]struct{}{}
	for _, param := range stmt.DefHeader.Params {
		extraAtomNames[param] = struct{}{}
	}

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

	return env.PropDefMem.Insert(stmt, glob.EmptyPkg)
}

func (env *Env) NewDefObj_InsideAtomsDeclared(stmt *ast.DefObjStmt) error {
	err := env.NonDuplicateParam_NoUndeclaredParamSet(stmt.Objs, stmt.ObjSets)
	if err != nil {
		return err
	}

	for _, fact := range stmt.NewInFacts() {
		if !env.AreAtomsInFactAreDeclared(fact, map[string]struct{}{}) {
			return fmt.Errorf(AtomsInFactNotDeclaredMsg(fact))
		}
		err := env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	for _, fact := range stmt.Facts {
		if !env.AreAtomsInFactAreDeclared(fact, map[string]struct{}{}) {
			return fmt.Errorf(AtomsInFactNotDeclaredMsg(fact))
		}
		err := env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	for _, objName := range stmt.Objs {
		err := env.isInvalidName(objName)
		if err != nil {
			return err
		}
	}

	return env.ObjDefMem.Insert(stmt, glob.EmptyPkg)
}

func (env *Env) NewDefFn_InsideAtomsDeclared(stmt *ast.DefFnStmt) error {
	err := env.NonDuplicateParam_NoUndeclaredParamSet(stmt.DefHeader.Params, stmt.DefHeader.SetParams)
	if err != nil {
		return err
	}
	ok := env.AreAtomsInFcAreDeclared(stmt.RetSet, map[string]struct{}{})
	if !ok {
		return fmt.Errorf(AtomsInFcNotDeclaredMsg(stmt.RetSet))
	}

	for _, fact := range stmt.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, map[string]struct{}{}) {
			return fmt.Errorf(fmt.Sprintf("%s\nis true by fn %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefHeader.Name))
		}
	}

	for _, fact := range stmt.ThenFacts {
		if !env.AreAtomsInFactAreDeclared(fact, map[string]struct{}{}) {
			return fmt.Errorf(fmt.Sprintf("%s\nis true by fn %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefHeader.Name))
		}
	}

	err = env.isInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	err = env.FnDefMem.Insert(stmt, glob.EmptyPkg)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) NewDefExistProp_InsideAtomsDeclared(stmt *ast.DefExistPropStmt) error {
	err := env.NonDuplicateParam_NoUndeclaredParamSet(append(stmt.DefBody.DefHeader.Params, stmt.ExistParams...), append(stmt.DefBody.DefHeader.SetParams, stmt.ExistParamSets...))
	if err != nil {
		return err
	}

	for _, fact := range stmt.DefBody.DomFacts {
		if !env.AreAtomsInFactAreDeclared(fact, map[string]struct{}{}) {
			return fmt.Errorf(fmt.Sprintf("%s\nis true by exist_prop %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefBody.DefHeader.Name))
		}
	}

	for _, fact := range stmt.DefBody.IffFacts {
		if !env.AreAtomsInFactAreDeclared(fact, map[string]struct{}{}) {
			return fmt.Errorf(fmt.Sprintf("%s\nis true by exist_prop %s definition, but there are undeclared atoms in the fact\n", fact.String(), stmt.DefBody.DefHeader.Name))
		}
	}

	err = env.isInvalidName(stmt.DefBody.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.ExistPropDefMem.Insert(stmt, glob.EmptyPkg)
}
