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
)

func successVerString(stmt, stmtVerifiedBy ast.Stmt) ast.VerRet {
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

	var stmtFact ast.FactStmt
	if stmt != nil {
		if factStmt, ok := stmt.(ast.FactStmt); ok {
			stmtFact = factStmt
		}
	}
	var ret ast.VerRet = ast.NewTrueVerRet(stmtFact, nil, "")
	for _, msg := range verifyMsgs {
		ret = ret.AddExtraInfo(msg)
	}
	return ret
}

// successVerStringString is a helper function for backward compatibility with string-based calls
func successVerStringString(stmtStr, stmtVerifiedByStr string) ast.VerRet {
	verifyMsgs := []string{}
	if stmtVerifiedByStr != "" {
		verifyMsgs = append(verifyMsgs, stmtVerifiedByStr)
	} else {
		verifyMsgs = append(verifyMsgs, "is true.")
	}

	var ret ast.VerRet = ast.NewTrueVerRet(nil, nil, "")
	for _, msg := range verifyMsgs {
		ret = ret.AddExtraInfo(msg)
	}
	return ret
}

func newMaybeSuccessMsgVerRet(state *VerState, stmt ast.Stmt, stmtVerifiedBy string) ast.VerRet {
	if state.WithMsg {
		return successVerStringString(stmt.String(), stmtVerifiedBy)
	}
	return ast.NewTrueVerRet(nil, nil, "")
}
