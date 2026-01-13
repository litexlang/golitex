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

func successVerString(stmt, stmtVerifiedBy ast.Stmt) *glob.VerRet {
	stmtStr := ""
	line := uint(0)
	if stmt != nil {
		stmtStr = stmt.String()
		if stmtVerifiedBy != nil {
			line = stmtVerifiedBy.GetLine()
		}
	}

	verifyMsgs := []string{}
	if stmtVerifiedBy != nil {
		if stmtVerifiedBy.GetLine() == 0 {
			verifyMsgs = append(verifyMsgs, stmtVerifiedBy.String())
		} else {
			verifyMsgs = append(verifyMsgs, stmtVerifiedBy.String())
		}
	} else {
		verifyMsgs = append(verifyMsgs, "is true.")
	}

	return glob.NewVerMsg(glob.StmtRetTypeTrue, stmtStr, line, verifyMsgs)
}

// successVerStringString is a helper function for backward compatibility with string-based calls
func successVerStringString(stmtStr, stmtVerifiedByStr string) *glob.VerRet {
	verifyMsgs := []string{}
	if stmtVerifiedByStr != "" {
		verifyMsgs = append(verifyMsgs, stmtVerifiedByStr)
	} else {
		verifyMsgs = append(verifyMsgs, "is true.")
	}

	return glob.NewVerMsg(glob.StmtRetTypeTrue, stmtStr, glob.BuiltinLine0, verifyMsgs)
}

func newMaybeSuccessMsgVerRet(state *VerState, stmt ast.Stmt, stmtVerifiedBy string) *glob.VerRet {
	if state.WithMsg {
		return successVerStringString(stmt.String(), stmtVerifiedBy)
	}
	return glob.NewEmptyVerRetTrue()
}
