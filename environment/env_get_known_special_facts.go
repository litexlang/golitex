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

import ast "golitex/ast"

func (e *Env) GetEnumFact(enumName string) ([]ast.Fc, bool) {
	for env := e; env != nil; env = env.Parent {
		enumFacts, ok := env.EnumFacts[enumName]
		if ok {
			return enumFacts, true
		}
	}

	return nil, false
}

func (e *Env) GetLatestFnT_GivenNameIsIn(fnName string) *FnInFnTMemItem {
	for env := e; env != nil; env = env.Parent {
		fnInFnTemplateFacts, ok := env.FnInFnTemplateFactsMem[fnName]
		if ok {
			return &fnInFnTemplateFacts[len(fnInFnTemplateFacts)-1]
		}
	}

	return nil
}

func (e *Env) IsTransitiveProp(propName string) bool {
	for env := e; env != nil; env = env.Parent {
		_, ok := env.TransitivePropMem[propName]
		if ok {
			return true
		}
	}
	return false
}

func (e *Env) GetRelatedFcSliceOfTransitiveProp(propName string, fc ast.Fc) []ast.Fc {
	ret := []ast.Fc{}
	for env := e; env != nil; env = env.Parent {
		relatedFcSlice, ok := env.TransitivePropMem[propName]
		if ok {
			if relatedFcSlice, ok := relatedFcSlice[fc.String()]; ok {
				ret = append(ret, relatedFcSlice...)
			}
		}
	}
	if len(ret) == 0 {
		return nil
	}
	return ret
}

func (e *Env) GetAlgoDef(funcName string) *ast.AlgoDefStmt {
	for env := e; env != nil; env = env.Parent {
		algoDef, ok := env.AlgoDefMem[funcName]
		if ok {
			return algoDef
		}
	}
	return nil
}
