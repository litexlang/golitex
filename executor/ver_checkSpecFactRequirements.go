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

func (ver *Verifier) checkSpecFactReq(stmt *ast.SpecFactStmt, state *VerState) (ExecRet, *VerState) {
	// if stmt.NameIs(glob.KeywordIn) {
	// 	verRet := ver.checkSpecFactReq_InFact_UseBtRules(stmt)
	// 	if verRet.IsErr() {
	// 		return verRet, state
	// 	}
	// 	if verRet.IsTrue() {
	// 		return verRet, state
	// 	}

	// 	state, verRet := ver.checkFnsReqAndUpdateReqState(stmt, state)
	// 	return verRet, state
	// }

	state, verRet := ver.checkFnsReqAndUpdateReqState(stmt, state)
	return verRet, state
}

// 只验证 1. params都声明了 2. 确实是fn template
// WARNING: 这个函数有严重的问题
// func (ver *Verifier) checkSpecFactReq_InFact_UseBtRules(stmt *ast.SpecFactStmt) ExecRet {
// 	ret := ver.Env.AreAtomsInFcAreDeclared(stmt.Params[0], map[string]struct{}{})
// 	if ret.IsErr() {
// 		return NewExecErr(ret.String())
// 	}

// 	if _, ok := stmt.Params[1].(*ast.FnObj); !ok {
// 		return NewExecUnknown("")
// 	}

// 	head, ok := stmt.Params[1].(*ast.FnObj).IsFcFn_HasAtomHead_ReturnHead() // WARNING: 这里有问题，因为可能不是fn template，而是 fn(R)R 这种
// 	// 需要处理 fn(R)R 这种；现在 fn_template 本质上也写成函数形式了
// 	if ok {
// 		def := ver.Env.GetFnTemplateDef(head)
// 		if def != nil {
// 			for _, param := range stmt.Params[1].(*ast.FnObj).Params {
// 				ret := ver.Env.AreAtomsInFcAreDeclared(param, map[string]struct{}{})
// 				if ret.IsErr() {
// 					return NewExecErr(ret.String())
// 				}
// 			}
// 			return NewExecTrue("")
// 		} else {
// 			ret := ver.Env.AreAtomsInFcAreDeclared(stmt.Params[1], map[string]struct{}{})
// 			if ret.IsErr() {
// 				return NewExecErr(ret.String())
// 			}
// 			return NewExecTrue("")
// 		}
// 	} else {
// 		ret := ver.Env.AreAtomsInFcAreDeclared(stmt.Params[1], map[string]struct{}{})
// 		if ret.IsErr() {
// 			return NewExecErr(ret.String())
// 		}

// 		return NewExecTrue("")
// 	}
// }
