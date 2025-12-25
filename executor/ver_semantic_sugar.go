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
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
)

func (ver *Verifier) verByReplaceObjInSpecFactWithValue(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	replaced, newStmt := ver.Env.ReplaceObjInSpecFactWithValue(stmt)
	if replaced {
		verRet := ver.verTrueEqualFactMainLogic(newStmt, state.CopyAndReqOkToFalse())
		if verRet.IsErr() {
			return NewExecErr("failed to verify true equal fact: " + verRet.String())
		}

		if verRet.IsTrue() {
			values := []ast.Obj{}
			if cmp.IsNumExprLitObj(newStmt.Params[0]) {
				values = append(values, newStmt.Params[0])
			} else {
				values = append(values, nil)
			}

			if cmp.IsNumExprLitObj(newStmt.Params[1]) {
				values = append(values, newStmt.Params[1])
			} else {
				values = append(values, nil)
			}

			var execRet ExecRet
			if values[0] == nil && values[1] == nil {
				execRet = NewExecTrue(fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
			} else {
				execRet = NewExecTrueWithValues(fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()), values)
			}
			msg := fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String())
			return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, execRet)
		}
	}

	return NewExecUnknown(fmt.Sprintf("%s is not equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
}

func (ver *Verifier) verByReplaceObjInSpecFactWithValueAndCompute(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	replaced, newStmt := ver.Env.ReplaceObjInSpecFactWithValue(stmt)

	if replaced {
		verRet := ver.verTrueEqualFactMainLogic(newStmt, state.CopyAndReqOkToFalse())
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			msg := fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values and computing", stmt.String(), newStmt.String())
			return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewEmptyExecTrue())
		}
	}

	return NewEmptyExecUnknown()
}
