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

// maybeAddSuccessMsg adds a success message to execRet if state.WithMsg is true
func (ver *Verifier) maybeAddSuccessMsg(state *VerState, stmt, stmtVerifiedBy ast.Stmt, execRet *glob.StmtRet) *glob.StmtRet {
	if state.WithMsg {
		execRet.AddVerifyProcess(successVerString(stmt, stmtVerifiedBy))
		return execRet
	}
	return execRet
}

// maybeAddSuccessMsgString is a backward compatibility function for string-based
func (ver *Verifier) maybeAddSuccessMsgString(state *VerState, stmtStr, verifiedByStr string, execRet *glob.StmtRet) *glob.StmtRet {
	if state == nil {
		panic("")
	}

	if state.WithMsg {
		execRet.AddVerifyProcess(successVerStringString(stmtStr, verifiedByStr))
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

// func ObjIsNotSet(obj ast.Obj) bool {
// 	return !ast.ObjIsKeywordSet(obj)
// }

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
