// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	cmp "golitex/litex_comparator"
	mem "golitex/litex_memory"
)

// match 函数不需要传入state: 没有any, spec 之分，也不需要打印
func (ver *Verifier) matchStoredUniSpecWithSpec(knownFact mem.StoredUniSpecFact, stmt *ast.SpecFactStmt) (map[string][]ast.Fc, bool, error) { // 之所以是map[string][]ast.Fc而不是 map[string]ast.Fc, 因为可能用户输入的是字面量相同，实际意义一样的obj
	if len(stmt.Params) != len(*knownFact.FuncParams) {
		return nil, false, nil
	}

	retMap := map[string][]ast.Fc{}

	for i, uniParam := range *knownFact.FuncParams {
		matchMap, matched, err := ver.matchUniFcWithConFc(uniParam, stmt.Params[i], knownFact.UniFact.Params)
		if err != nil {
			return nil, false, err
		}
		if !matched {
			return nil, false, nil
		}
		mergeMatchMaps(matchMap, retMap)
	}

	return retMap, true, nil
}

func (ver *Verifier) matchUniFcWithConFc(uniFuncParam ast.Fc, concreteFuncParam ast.Fc, possibleUniParams []string) (map[string][]ast.Fc, bool, error) {
	// 注意到，如果传入的不是fn，而是atom，那大概率是不能match上的。只有一种例外:
	// know forall x A: $p(x *(3-2)); $p(1*1) 这时候 3 -2 要能和1对上。而 uniFunc 的对应关系，只是让自由变量去对应，不包括builtinFc的match
	// 同时，也不能直接去CmpFcRule，因为如果输入的变量的字面量刚好是存着的自由变量的字面量，那恰好相等了，这是不行的。只能是BuiltinFc 之间相等
	// 为了处理这种情况，引入下面这段代码
	ok, err := cmp.BuiltinFcEqualRule(uniFuncParam, concreteFuncParam)
	if err != nil {
		return nil, false, err
	}
	if ok {
		return make(map[string][]ast.Fc), true, nil
	}

	// Safe type switching
	switch param := uniFuncParam.(type) {
	case *ast.FcAtom:
		return ver.matchAtomUniWithConFc(param, concreteFuncParam, possibleUniParams)
	case *ast.FcFn:
		return ver.matchFnUniWithConFc(param, concreteFuncParam, possibleUniParams)
	default:
		return nil, false, fmt.Errorf("unexpected type %T for parameter %v", param, uniFuncParam.String())
	}
}

func (ver *Verifier) matchAtomUniWithConFc(uniFuncFcAtom *ast.FcAtom, conFuncParam ast.Fc, possibleUniParams []string) (map[string][]ast.Fc, bool, error) {
	retMap := make(map[string][]ast.Fc)

	if matchStr, ok := isUniParam(uniFuncFcAtom, possibleUniParams); ok {
		retMap[matchStr] = []ast.Fc{conFuncParam}
		return retMap, true, nil
	}

	ok, err := ver.fcEqualSpec(uniFuncFcAtom, conFuncParam, SpecNoMsg)
	if err != nil {
		return nil, false, err
	}
	if ok {
		return retMap, true, nil
	}

	return nil, false, nil
}

func (ver *Verifier) matchFnUniWithConFc(uniFuncFcFn *ast.FcFn, conFuncParam ast.Fc, possibleUniParams []string) (map[string][]ast.Fc, bool, error) {
	retMap := map[string][]ast.Fc{}

	conParamAsFcFn, ok := conFuncParam.(*ast.FcFn)
	if !ok {
		return nil, false, nil
	}

	if matchedStr, ok := isUniParam(&uniFuncFcFn.FnHead, possibleUniParams); ok {
		retMap[matchedStr] = []ast.Fc{&conParamAsFcFn.FnHead}
	} else {
		ok, err := ver.fcEqualSpec(&uniFuncFcFn.FnHead, &conParamAsFcFn.FnHead, SpecNoMsg)
		if err != nil {
			return nil, false, err
		}
		if !ok {
			return nil, false, nil
		}
	}

	if len(conParamAsFcFn.ParamSegs) != len(uniFuncFcFn.ParamSegs) {
		return nil, false, nil //? 不清楚应该报错还是说直接返回不对，应该是返回不对
	}

	for i, uniPipe := range uniFuncFcFn.ParamSegs {
		if len(uniPipe) != len(conParamAsFcFn.ParamSegs[i]) {
			return nil, false, nil
		}

		for j, param := range uniPipe {
			matchMap, ok, err := ver.matchUniFcWithConFc(param, conParamAsFcFn.ParamSegs[i][j], possibleUniParams)
			if err != nil {
				return nil, false, err
			}
			if !ok {
				return nil, false, nil
			}
			mergeMatchMaps(matchMap, retMap)
		}
	}

	return retMap, true, nil
}

func isUniParam(uniFuncAtom *ast.FcAtom, possibleUniParams []string) (string, bool) { // ret: matched possible uniParam string; isMatched?
	for _, possible := range possibleUniParams {
		if possible == uniFuncAtom.Name && uniFuncAtom.PkgName == "" {
			return possible, true
		}
	}
	return "", false
}

func mergeMatchMaps(from map[string][]ast.Fc, to map[string][]ast.Fc) {
	for key, value := range from {
		if _, ok := (to)[key]; ok {
			(to)[key] = append((to)[key], value...)
		} else {
			(to)[key] = value
		}
	}
}
