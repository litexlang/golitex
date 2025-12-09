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

package litex_executor

import (
	ast "golitex/ast"
)

func (ver *Verifier) evaluateNonNumberLiteralExpr(obj ast.Obj) ast.Obj {
	if objAsFn, ok := obj.(*ast.FnObj); ok {
		// 尝试简化 set_dim(cart(...))
		if simplified, replaced := ast.SimplifyDimCart(objAsFn); replaced {
			return simplified
		}
		// 尝试简化 proj(cart(...), n)
		if simplified, replaced := ast.SimplifyProjCart(objAsFn); replaced {
			return simplified
		}
		// 如果是 [] 函数，从环境里读取 equalTo tuple 的东西出来，或者直接从 tuple 中读取
		if ast.IsIndexOptFnObj(objAsFn) && len(objAsFn.Params) == 2 {
			obj := objAsFn.Params[0]
			indexObj := objAsFn.Params[1]

			// 尝试将 index 转换为整数
			index, ok := ast.ToInt(indexObj)
			if !ok {
				return obj
			}

			// 情况1: obj 本身就是一个 tuple，比如 (1,2)[1]
			if objAsTuple, ok := obj.(*ast.FnObj); ok && ast.IsTupleFnObj(objAsTuple) {
				if index >= 1 && index <= len(objAsTuple.Params) {
					// 索引从 1 开始，所以需要减 1
					return objAsTuple.Params[index-1]
				}
			}

			// 情况2: 从环境里读取 equalTo tuple 的东西出来
			tuple := ver.Env.GetObjTuple(obj)
			if tuple != nil {
				if tupleAsFn, ok := tuple.(*ast.FnObj); ok && ast.IsTupleFnObj(tupleAsFn) {
					if index >= 1 && index <= len(tupleAsFn.Params) {
						// 索引从 1 开始，所以需要减 1
						return tupleAsFn.Params[index-1]
					}
				}
			}
		}
	}

	return obj
}
