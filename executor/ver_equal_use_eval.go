// Copyright Jiachen Shen.
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

package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) GetValueOfSymbol(obj ast.Obj) (bool, ast.Obj) {
	newReplaced, newObj := ver.Env.GetStoredSymbolValue(obj)

	if newReplaced {
		return true, newObj
	}

	if objAsFn, ok := obj.(*ast.FnObj); ok {
		// val(...) should be evaluated (like eval)
		if ast.IsAtomObjAndEqualToStr(objAsFn.FnHead, glob.KeywordVal) && len(objAsFn.Params) == 1 {
			exec := NewExecutor(ver.Env)
			exec.NewEnv()
			defer exec.deleteEnv()
			value, execRet := exec.evalObjThenSimplify(objAsFn.Params[0])
			if execRet.IsTrue() {
				return true, value
			}
		}
		// 尝试简化 set_dim(cart(...))
		if simplified, replaced := ast.SimplifyDimCart(objAsFn); replaced {
			return true, simplified
		}
		// 尝试简化 proj(cart(...), n)
		if simplified, replaced := ast.SimplifyProjCart(objAsFn); replaced {
			return true, simplified
		}

		// 如果是 [] 函数，从环境里读取 equalTo tuple 的东西出来，或者直接从 tuple 中读取
		if replaced, value := ver.evaluateIndexOperation(objAsFn); replaced {
			return true, value
		}

	}

	return false, obj
}

// evaluateIndexOperation 处理索引操作 []，从环境里读取 equalTo tuple 的东西出来，或者直接从 tuple 中读取
func (ver *Verifier) evaluateIndexOperation(objAsFn *ast.FnObj) (bool, ast.Obj) {
	if !ast.IsIndexOptFnObj(objAsFn) || len(objAsFn.Params) != 2 {
		return false, nil
	}

	obj := objAsFn.Params[0]
	indexObj := objAsFn.Params[1]

	// 尝试将 index 转换为整数
	index, ok := ast.ToInt(indexObj)
	if !ok {
		return false, nil
	}

	// 情况1: obj 本身就是一个 tuple，比如 (1,2)[1]
	if objAsTuple, ok := obj.(*ast.FnObj); ok && ast.IsTupleFnObj(objAsTuple) {
		if index >= 1 && index <= len(objAsTuple.Params) {
			// 索引从 1 开始，所以需要减 1
			return true, objAsTuple.Params[index-1]
		}
	}

	// 情况2: 从环境里读取 equalTo tuple 的东西出来
	tuple := ver.Env.GetObjTuple(obj)
	if tuple != nil {
		if tupleAsFn, ok := tuple.(*ast.FnObj); ok && ast.IsTupleFnObj(tupleAsFn) {
			if index >= 1 && index <= len(tupleAsFn.Params) {
				// 索引从 1 开始，所以需要减 1
				return true, tupleAsFn.Params[index-1]
			}
		}
	}

	return false, nil
}
