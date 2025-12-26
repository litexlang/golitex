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

func (ver *Verifier) verSpecialFactInSpecialWays(stmt *ast.SpecFactStmt, state *VerState) *glob.GlobRet {
	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeySymbolLargerEqual) {
		return ver.verGreaterEqualBySpecialWays(stmt, state)
	}

	// 如果是 <= 那可以用 < 和 = 来证明，针对sqrt里不能对负数开方额外做的
	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeySymbolLessEqual) {
		return ver.verLessEqualBySpecialWays(stmt, state)
	}

	// 如果是 != 0, 可以用 > 0 证明，可以用 < 0 证明。针对除法分母不为0额外做的
	// Example: 如果没有这里的特殊证明，下面的g(2) / g(f(1)) = g(2) / g(f(1)) 无法证明
	// 	fn f(x R) R:
	//     dom:
	//         x >= 0
	//     =>:
	//         f(x) = x + 1

	// fn g(x R) R

	// know forall x R: x > 0 => g(x) > 0

	// know forall x R: x > 0 => f(x) > 0

	// f(1) > 0

	// g(2) / g(f(1)) = g(2) / g(f(1))
	if ast.IsFalseSpecFactWithPropName(stmt, glob.KeySymbolEqual) && len(stmt.Params) == 2 {
		// 检查是否是 != 0 的情况
		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], "0") {
			return ver.verNotEqualZeroBySpecialWays(stmt, state)
		} else {
			// 如果要证明 a != b，可以用 a - b != 0 或 a > b 或 a < b 来证明
			return ver.verNotEqualBySpecialWays(stmt, state)
		}
	}

	return glob.NewEmptyGlobUnknown()
}

// 如果是 >= 那可以用 > 和 = 来证明，针对sqrt里不能对负数开方额外做的
// Example: 如果没有这里的特殊证明，下面的f(g(1)) = f(g(1)) 无法证明
// 	fn f(x R) R:
//     dom:
//         x >= 0
//     =>:
//         f(x) = x + 1

// fn g(x R) R

// know:
//     forall x R: x > 0 => g(x) > 0

// f(g(1)) = f(g(1))
func (ver *Verifier) verGreaterEqualBySpecialWays(stmt *ast.SpecFactStmt, state *VerState) *glob.GlobRet {
	if len(stmt.Params) != 2 {
		return glob.NewEmptyGlobUnknown()
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
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
	}

	// 如果 > 不成立，尝试用 = 证明
	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, right}, stmt.Line)
	verRet = ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(equalFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), equalFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
	}

	return glob.NewEmptyGlobUnknown()
}

func (ver *Verifier) verLessEqualBySpecialWays(stmt *ast.SpecFactStmt, state *VerState) *glob.GlobRet {
	if len(stmt.Params) != 2 {
		return glob.NewEmptyGlobUnknown()
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
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
	}

	// 如果 < 不成立，尝试用 = 证明
	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, right}, stmt.Line)
	verRet = ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(equalFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), equalFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
	}

	return glob.NewEmptyGlobUnknown()
}

func (ver *Verifier) verNotEqualZeroBySpecialWays(stmt *ast.SpecFactStmt, state *VerState) *glob.GlobRet {
	if len(stmt.Params) != 2 {
		return glob.NewEmptyGlobUnknown()
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
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
	}

	// 如果 > 0 不成立，尝试用 < 0 证明
	lessFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{left, right}, stmt.Line)
	verRet = ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(lessFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), lessFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
	}

	// 如果 a != b 那 a - b != 0
	if IsObjMinusFnObj(left) && right.String() == "0" {
		leftLeft := left.(*ast.FnObj).Params[0]
		leftRight := left.(*ast.FnObj).Params[1]

		notEqualFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{leftLeft, leftRight}, glob.BuiltinLine)

		verRet = ver.verSpecFactThatIsNotTrueEqualFact_UseCommutativity(notEqualFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			msg := fmt.Sprintf("%s is proved by %s", stmt.String(), notEqualFact.String())
			return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
		}
	}

	return glob.NewEmptyGlobUnknown()
}

func (ver *Verifier) verNotEqualBySpecialWays(stmt *ast.SpecFactStmt, state *VerState) *glob.GlobRet {
	if len(stmt.Params) != 2 {
		return glob.NewEmptyGlobUnknown()
	}

	left := stmt.Params[0]
	right := stmt.Params[1]

	// 如果要证明 a != b，可以用 a > b 或 a < b 或 a - b != 0 来证明
	// 先尝试用 > 证明
	greaterFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{left, right}, stmt.Line)
	verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(greaterFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), greaterFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
	}

	// 如果 > 不成立，尝试用 < 证明
	lessFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{left, right}, stmt.Line)
	verRet = ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(lessFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s", stmt.String(), lessFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
	}

	// 如果 > 和 < 都不成立，尝试用 a - b != 0 证明
	subExpr := ast.NewFnObj(ast.Atom(glob.KeySymbolMinus), []ast.Obj{left, right})
	subNotEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{subExpr, ast.Atom("0")}, stmt.Line)
	verRet = ver.VerFactStmt(subNotEqualZeroFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("%s is proved by %s (if a - b != 0 then a != b)", stmt.String(), subNotEqualZeroFact.String())
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyGlobTrue())
	}

	return glob.NewEmptyGlobUnknown()
}

func IsObjMinusFnObj(obj ast.Obj) bool {
	asFn, ok := obj.(*ast.FnObj)
	if !ok {
		return false
	}

	if len(asFn.Params) != 2 {
		return false
	}

	if asFn.FnHead.String() == glob.KeySymbolMinus {
		return true
	}

	return false
}
