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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_env

import (
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

func (env *Env) NewDefProp(stmt *ast.DefPropStmt) error {
	err := env.isInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.PropDefMem.Insert(stmt, glob.EmptyPkg)
}

func (env *Env) NewDefObj(stmt *ast.DefObjStmt) error {
	for _, objName := range stmt.Objs {
		err := env.isInvalidName(objName)
		if err != nil {
			return err
		}
	}

	return env.ObjDefMem.Insert(stmt, glob.EmptyPkg)
}

func (env *Env) NewDefFn(stmt *ast.DefFnStmt) error {
	err := env.isInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	err = env.FnDefMem.Insert(stmt, glob.EmptyPkg)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) NewDefExistProp(stmt *ast.DefExistPropStmt) error {
	err := env.isInvalidName(stmt.DefBody.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.ExistPropDefMem.Insert(stmt, glob.EmptyPkg)
}
