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
	ast "golitex/ast"
	cmp "golitex/cmp"
	"strconv"
)

func (env *Env) ReplaceSymbolWithValue(fc ast.Obj) (bool, ast.Obj) {
	if cmp.IsNumExprLitObj(fc) {
		return false, fc
	}

	switch asFc := fc.(type) {
	case ast.Atom:
		return env.GetValueOfAtomObj(asFc)
	case *ast.FnObj:
		return env.GetValueOfFnObj(asFc)
	}
	panic("")
}

func (env *Env) IsIndexOfTupleFnObjAndGetValueAtIndex(fc *ast.FnObj) (bool, ast.Obj) {
	if ast.IsIndexOptFnObj(fc) && ast.IsTupleObj(fc.Params[0]) {
		value := getTupleValueAtIndex(fc.Params[0].(*ast.FnObj), fc.Params[1])
		if value != nil {
			_, valueOfValue := env.ReplaceSymbolWithValue(value)
			return true, valueOfValue
		}
		return false, nil
	}

	return false, nil
}

func getTupleValueAtIndex(tuple *ast.FnObj, index ast.Obj) ast.Obj {
	if asAtom, ok := index.(ast.Atom); ok {
		// string(asAtom) 是整数
		index, err := strconv.Atoi(string(asAtom))
		if err != nil {
			return nil
		}

		if index >= 1 && index <= len(tuple.Params) {
			return tuple.Params[index-1]
		}

		return nil
	}

	return nil
}

func (env *Env) GetValueOfFnObj(fc *ast.FnObj) (bool, ast.Obj) {
	if ok, value := env.IsIndexOfTupleFnObjAndGetValueAtIndex(fc); ok {
		return true, value
	}

	if symbolValue := env.GetSymbolSimplifiedValue(fc); symbolValue != nil {
		return true, symbolValue
	}

	replaced := false
	newParams := make([]ast.Obj, len(fc.Params))
	for i, param := range fc.Params {
		var newReplaced bool
		newReplaced, newParams[i] = env.ReplaceSymbolWithValue(param)

		replaced = replaced || newReplaced
	}
	return replaced, ast.NewFnObj(fc.FnHead, newParams)
}

func (env *Env) GetValueOfAtomObj(fc ast.Atom) (bool, ast.Obj) {
	symbolValue := env.GetSymbolSimplifiedValue(fc)
	if symbolValue == nil {
		return false, fc
	}

	return true, symbolValue
}

func (env *Env) ReplaceFcInSpecFactWithValue(fact *ast.SpecFactStmt) (bool, *ast.SpecFactStmt) {
	newParams := make([]ast.Obj, len(fact.Params))
	replaced := false
	for i, param := range fact.Params {
		var newReplaced bool
		newReplaced, newParams[i] = env.ReplaceSymbolWithValue(param)

		replaced = replaced || newReplaced
	}
	return replaced, ast.NewSpecFactStmt(fact.TypeEnum, fact.PropName, newParams, fact.Line)
}
