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
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt *ast.SpecFactStmt) *env.Env {
	_ = stmt
	return nil
}

// func (ver *Verifier) processOkMsg(state *VerState, msg string, verifiedBy string, args ...any) ExecRet {
// 	// Note: processOkMsg uses string format, keep using string version for backward compatibility
// 	verifiedByStr := fmt.Sprintf(verifiedBy, args...)
// 	execRet := NewExecTrue(successVerStringString(msg, verifiedByStr))
// 	if state.WithMsg {
// 		execRet.AddMsg(successVerStringString(msg, verifiedByStr))
// 		return execRet
// 	}
// 	return execRet
// }

// maybeAddSuccessMsg adds a success message to execRet if state.WithMsg is true
func (ver *Verifier) maybeAddSuccessMsg(state *VerState, stmt, stmtVerifiedBy ast.Stmt, execRet ExecRet) ExecRet {
	if state.WithMsg {
		execRet.AddMsg(successVerString(stmt, stmtVerifiedBy))
		return execRet
	}
	return execRet
}

// maybeAddSuccessMsgString is a backward compatibility function for string-based messages
func (ver *Verifier) maybeAddSuccessMsgString(state *VerState, stmtStr, verifiedByStr string, execRet ExecRet) ExecRet {
	if state.WithMsg {
		execRet.AddMsg(successVerStringString(stmtStr, verifiedByStr))
		return execRet
	}
	return execRet
}

func IsTrueOrErr(ok bool, err error) bool {
	return ok || err != nil
}

func IsFalseOrErr(ok bool, err error) bool {
	return !ok || err != nil
}

func ObjIsNotSet(obj ast.Obj) bool {
	return obj.String() != glob.KeywordSet
}

// ordinalSuffix converts a number to its ordinal form (1st, 2nd, 3rd, 4th, etc.)
func ordinalSuffix(n int) string {
	if n < 0 {
		return fmt.Sprintf("%dth", n)
	}

	// Special cases for 11, 12, 13 which all use "th"
	if n%100 >= 11 && n%100 <= 13 {
		return fmt.Sprintf("%dth", n)
	}

	// Regular cases based on last digit
	switch n % 10 {
	case 1:
		return fmt.Sprintf("%dst", n)
	case 2:
		return fmt.Sprintf("%dnd", n)
	case 3:
		return fmt.Sprintf("%drd", n)
	default:
		return fmt.Sprintf("%dth", n)
	}
}
