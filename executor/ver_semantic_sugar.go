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
	if replaced {
		verRet := ver.verTrueEqualFactMainLogic(newStmt, state.CopyAndReqOkToFalse())
		if verRet.IsErr() {
			return glob.NewVerMsg2(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{"failed to verify true equal fact: " + verRet.String()})
		}

		if verRet.IsTrue() {
			msg := fmt.Sprintf("proved by replacing the symbols with their values:\n%s", newStmt.String())
			if state.WithMsg {
				return glob.NewVerMsg2(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{msg})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}

	return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("%s is not equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String())})
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
