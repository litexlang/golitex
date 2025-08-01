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

func (e *Env) GetLatestFnTT_GivenNameIsIn(fnName string) (*FnInFnTTMemItem, bool) {
	for env := e; env != nil; env = env.Parent {
		fnInFnTemplateFacts, ok := env.FnInFnTemplateFactsMem[fnName]
		if ok {
			return &fnInFnTemplateFacts[len(fnInFnTemplateFacts)-1], true
		}
	}

	return nil, false
}

func (e *Env) GetFnTemplateSliceTheFnIsIn(fnName string) ([]FnInFnTTMemItem, bool) {
	ret := []FnInFnTTMemItem{}
	for env := e; env != nil; env = env.Parent {
		fnInFnTemplateFacts, ok := env.FnInFnTemplateFactsMem[fnName]
		if ok {
			ret = append(ret, fnInFnTemplateFacts...)
		}
	}
	if len(ret) == 0 {
		return nil, false
	}

	return ret, true
}
