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
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verByReplaceObjInSpecFactWithValue(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	replaced, newStmt := ver.Env.ReplaceObjInSpecFactWithValue(stmt)

	// After replacing symbols with values, evaluate any val(...) expressions
	newParams := make([]ast.Obj, len(newStmt.Params))
	valReplaced := false
	for i, param := range newStmt.Params {
		if fnObj, ok := param.(*ast.FnObj); ok {
			if ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeywordVal) && len(fnObj.Params) == 1 {
				// val(...) should be evaluated (like eval)
				exec := NewExecutor(ver.Env)
				exec.NewEnv()
				defer exec.deleteEnv()
				value, execRet := exec.evalObjThenSimplify(fnObj.Params[0])
				if execRet.IsTrue() {
					newParams[i] = value
					valReplaced = true
					continue
				}
			}
		}
		newParams[i] = param
	}

	if valReplaced {
		newStmt = ast.NewSpecFactStmt(newStmt.FactType, newStmt.PropName, newParams, newStmt.Line)
		replaced = true
	}

	if replaced {
		verRet := ver.verTrueEqualFactMainLogic(newStmt, state.CopyAndReqOkToFalse())
		if verRet.IsErr() {
			return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{"failed to verify true equal fact: " + verRet.String()})
		}

		if verRet.IsTrue() {
			msg := fmt.Sprintf("proved by replacing the symbols with their values:\n%s", newStmt.String())
			if state.WithMsg {
				return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{msg})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}

	return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("%s is not equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String())})
}

// func (ver *Verifier) verByReplaceObjInSpecFactWithValueAndCompute(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
// 	replaced, newStmt := ver.Env.ReplaceObjInSpecFactWithValue(stmt)

// 	if replaced {
// 		verRet := ver.verTrueEqualFactMainLogic(newStmt, state.CopyAndReqOkToFalse())
// 		if verRet.IsErr() {
// 			return verRet
// 		}
// 		if verRet.IsTrue() {
// 			msg := fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values and computing", stmt.String(), newStmt.String())
// 			if state.WithMsg {
// 				return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), stmt.Line, []string{msg})
// 			}
// 			return glob.NewEmptyVerRetTrue()
// 		}
// 	}

// 	return glob.NewEmptyVerRetUnknown()
// }
