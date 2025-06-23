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
)

func (e *Env) GetFnTemplateOfGivenFc(fn ast.Fc) ([]*ast.FnTemplateStmt, bool) {
	fnDefs := []*ast.FnTemplateStmt{}
	for env := e; env != nil; env = env.Parent {
		fnDefsFromEnv, ok := env.FnInFnTemplateFactsMem.Get(fn)
		if ok {
			fnDefs = append(fnDefs, fnDefsFromEnv...)
		}
	}
	return fnDefs, true
}

func (e *Env) getFcAtomDefAtCurEnv(fcAtomName *ast.FcAtom) bool {
	// Case1: It is a prop
	_, ok := e.PropDefMem.Get(*fcAtomName)
	if ok {
		return true
	}

	// Case3: It is a exist prop
	_, ok = e.ExistPropDefMem.Get(*fcAtomName)
	if ok {
		return true
	}

	// Case4: It is a obj
	_, ok = e.ObjDefMem.Get(*fcAtomName)
	if ok {
		return true
	}

	// Case5: It is a fn template
	_, ok = e.FnTemplateDefMem.Get(*fcAtomName)

	return ok
}

func (e *Env) GetTemplateOfFn(fc *ast.FcFn) (*ast.FnTemplateStmt, bool) {
	if fcHeadAsAtom, ok := fc.FnHead.(*ast.FcAtom); ok {
		fnDef, ok := e.GetLatestFnTemplate(fcHeadAsAtom)
		if !ok {
			return nil, false
		}

		return fnDef, true
	} else {
		fcHeadAsFn, ok := fc.FnHead.(*ast.FcFn)
		if !ok {
			return nil, false
		}

		return e.GetTemplateOfFn(fcHeadAsFn)
	}
}

func (e *Env) NewObj_CheckValidName(name string) error {
	if !e.IsValidObjName(name) {
		return fmt.Errorf("invalid name: %s", name)
	}

	err := e.ObjDefMem.Insert(name)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) IsValidObjName(name string) bool {
	if glob.IsValidUserDefinedName(name) != nil {
		return false
	}

	if e.GetFcAtomDef(ast.NewFcAtomWithName(name)) {
		return false
	}

	return true
}
