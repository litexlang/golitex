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
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) ReplaceSymbolWithValue(obj ast.Obj) (bool, ast.Obj) {
	if cmp.IsNumExprLitObj(obj) {
		return false, obj
	}

	switch asObj := obj.(type) {
	case ast.Atom:
		return envMgr.GetValueOfAtomObj(asObj)
	case *ast.FnObj:
		return envMgr.GetValueOfFnObj(asObj)
	}
	panic("")
}

func (envMgr *EnvMgr) IsIndexOfTupleFnObjAndGetValueAtIndex(obj *ast.FnObj) (bool, ast.Obj) {
	if ast.IsIndexOptFnObj(obj) && ast.IsTupleObj(obj.Params[0]) {
		value := getTupleValueAtIndex(obj.Params[0].(*ast.FnObj), obj.Params[1])
		if value != nil {
			_, valueOfValue := envMgr.ReplaceSymbolWithValue(value)
			return true, valueOfValue
		}
		return false, nil
	}

	return false, nil
}

func (envMgr *EnvMgr) GetValueOfFnObj(obj *ast.FnObj) (bool, ast.Obj) {
	if ok, value := envMgr.IsIndexOfTupleFnObjAndGetValueAtIndex(obj); ok {
		return true, value
	}

	// 如果是 count(listSet)，计算 list set 的元素个数
	if ast.IsAtomObjAndEqualToStr(obj.FnHead, glob.KeywordCount) && len(obj.Params) == 1 {
		// 先对参数进行值替换
		_, replacedParam := envMgr.ReplaceSymbolWithValue(obj.Params[0])
		if ast.IsListSetObj(replacedParam) {
			listSet := replacedParam.(*ast.FnObj)
			count := len(listSet.Params)
			return true, ast.Atom(fmt.Sprintf("%d", count))
		}
	}

	if symbolValue := envMgr.GetSymbolSimplifiedValue(obj); symbolValue != nil {
		return true, symbolValue
	}

	replaced := false
	newParams := make([]ast.Obj, len(obj.Params))
	for i, param := range obj.Params {
		var newReplaced bool
		newReplaced, newParams[i] = envMgr.ReplaceSymbolWithValue(param)

		replaced = replaced || newReplaced
	}
	return replaced, ast.NewFnObj(obj.FnHead, newParams)
}

func (envMgr *EnvMgr) GetValueOfAtomObj(obj ast.Atom) (bool, ast.Obj) {
	symbolValue := envMgr.GetSymbolSimplifiedValue(obj)
	if symbolValue == nil {
		return false, obj
	}

	return true, symbolValue
}

func (envMgr *EnvMgr) ReplaceObjInSpecFactWithValue(fact *ast.SpecFactStmt) (bool, *ast.SpecFactStmt) {
	newParams := make([]ast.Obj, len(fact.Params))
	replaced := false
	for i, param := range fact.Params {
		var newReplaced bool
		newReplaced, newParams[i] = envMgr.ReplaceSymbolWithValue(param)

		replaced = replaced || newReplaced
	}
	return replaced, ast.NewSpecFactStmt(fact.TypeEnum, fact.PropName, newParams, fact.Line)
}

