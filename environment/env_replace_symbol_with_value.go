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
)

func (env *Env) ReplaceSymbolWithValue(fc ast.Fc) ast.Fc {
	switch asFc := fc.(type) {
	case ast.FcAtom:
		return env.replaceFcAtomWithValue(asFc)
	case *ast.FcFn:
		return env.replaceFcFnWithValue(asFc)
	}
	return fc
}

func (env *Env) replaceFcFnWithValue(fc *ast.FcFn) ast.Fc {
	if symbolValue, ok := env.GetSymbolValue(fc); ok {
		return symbolValue
	}

	newParams := make([]ast.Fc, len(fc.Params))
	for i, param := range fc.Params {
		newParams[i] = env.ReplaceSymbolWithValue(param)
	}
	return ast.NewFcFn(fc.FnHead, newParams)
}

func (env *Env) replaceFcAtomWithValue(fc ast.FcAtom) ast.Fc {
	symbolValue, ok := env.GetSymbolValue(fc)
	if !ok {
		return fc
	}
	return symbolValue
}

func (env *Env) ReplaceFcInEqualFact(fact *ast.SpecFactStmt) *ast.SpecFactStmt {
	newParams := make([]ast.Fc, len(fact.Params))
	for i, param := range fact.Params {
		newParams[i] = env.ReplaceSymbolWithValue(param)
	}
	return ast.NewSpecFactStmt(fact.TypeEnum, fact.PropName, newParams, fact.Line)
}
