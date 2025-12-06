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
	glob "golitex/glob"
)

func (ver *Verifier) verSpecialFactInSpecialWays(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// 如果是 >= 那可以用 > 和 = 来证明，针对sqrt里不能对负数开方额外做的
	if stmt.NameIs(glob.KeySymbolLargerEqual) && stmt.TypeEnum == ast.TruePure {
		return ver.verGreaterEqualBySpecialWays(stmt, state)
	}

	// 如果是 <= 那可以用 < 和 = 来证明，针对sqrt里不能对负数开方额外做的
	if stmt.NameIs(glob.KeySymbolLessEqual) && stmt.TypeEnum == ast.TruePure {
		return ver.verLessEqualBySpecialWays(stmt, state)
	}

	// 如果是 != 0, 可以用 > 0 证明，可以用 < 0 证明。针对除法分母不为0额外做的
	if stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.FalsePure && len(stmt.Params) == 2 {
		// 检查是否是 != 0 的情况
		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], "0") {
			return ver.verNotEqualZeroBySpecialWays(stmt, state)
		}
	}

	return NewExecUnknown("")
}

func (ver *Verifier) verGreaterEqualBySpecialWays(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(stmt.Params) != 2 {
		return NewExecUnknown("")
	}

	left := stmt.Params[0]
	right := stmt.Params[1]

	// 处理 >= 的情况: a >= b 等价于 (a > b) or (a = b)
	// 先尝试用 > 证明
	greaterFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{left, right}, stmt.Line)
	verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(greaterFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), greaterFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
	}

	// 如果 > 不成立，尝试用 = 证明
	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, right}, stmt.Line)
	verRet = ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(equalFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), equalFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
	}

	return NewExecUnknown("")
}

func (ver *Verifier) verLessEqualBySpecialWays(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(stmt.Params) != 2 {
		return NewExecUnknown("")
	}

	left := stmt.Params[0]
	right := stmt.Params[1]

	// 处理 <= 的情况: a <= b 等价于 (a < b) or (a = b)
	// 先尝试用 < 证明
	lessFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{left, right}, stmt.Line)
	verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(lessFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), lessFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
	}

	// 如果 < 不成立，尝试用 = 证明
	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, right}, stmt.Line)
	verRet = ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(equalFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), equalFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
	}

	return NewExecUnknown("")
}

func (ver *Verifier) verNotEqualZeroBySpecialWays(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(stmt.Params) != 2 {
		return NewExecUnknown("")
	}

	left := stmt.Params[0]
	right := stmt.Params[1]

	// 处理 != 0 的情况: a != 0 等价于 (a > 0) or (a < 0)
	// 先尝试用 > 0 证明
	greaterFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{left, right}, stmt.Line)
	verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(greaterFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), greaterFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
	}

	// 如果 > 0 不成立，尝试用 < 0 证明
	lessFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{left, right}, stmt.Line)
	verRet = ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(lessFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), lessFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
	}

	return NewExecUnknown("")
}
