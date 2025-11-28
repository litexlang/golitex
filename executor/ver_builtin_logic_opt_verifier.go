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

func (ver *Verifier) verNumberLogicRelaOpt_BuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if !stmt.IsTrue() {
		return NewExecUnknown("")
	}

	verRet := ver.btNumberInfixCompareProp(stmt, state)
	if verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	// 如果left是 N_pos中元素，右侧是任何小于1的数字字面量，那就大于
	verRet = ver.nPosElementGreaterThanLessThanOne(stmt, state)
	if verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return NewExecUnknown("")
}

func (ver *Verifier) btNumberInfixCompareProp(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if !glob.IsBuiltinNumberInfixRelaProp(string(stmt.PropName)) {
		return NewExecUnknown("")
	}

	if len(stmt.Params) != 2 {
		return NewExecErr(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	leftNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if !ok {
		return NewExecUnknown("")
	}

	rightNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[1])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if !ok {
		return NewExecUnknown("")
	}

	ok, err = glob.NumLitExprCompareOpt(leftNumLitExpr, rightNumLitExpr, string(stmt.PropName))

	if err != nil {
		return NewExecErr(err.Error())
	}
	if ok {
		return ver.maybeAddSuccessMsg(state, stmt.String(), "builtin rules", NewExecTrue(""))
	}

	return NewExecUnknown("")
}

func (ver *Verifier) btLitNumInNatOrIntOrRatOrRealOrComplex(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if stmt.PropName != glob.KeywordIn {
		return NewExecUnknown("")
	}

	// Note: Messages should be handled by the caller, not in defer functions
	isSuccess := false
	defer func() {
		_ = isSuccess
	}()

	if len(stmt.Params) != 2 {
		return NewExecErr(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	leftFc, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if ok {
		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftFc)
			if isSuccess {
				return NewExecTrue("")
			} else {
				return NewExecUnknown("")
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftFc)
			if isSuccess {
				return NewExecTrue("")
			} else {
				return NewExecUnknown("")
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordInteger) {
			isSuccess = glob.IsIntegerNumLitExpr(leftFc)
			if isSuccess {
				return NewExecTrue("")
			} else {
				return NewExecUnknown("")
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftFc)
			if isSuccess {
				return NewExecTrue("")
			} else {
				return NewExecUnknown("")
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordComplex) {
			isSuccess = glob.IsComplexNumLitExpr(leftFc)
			if isSuccess {
				return NewExecTrue("")
			} else {
				return NewExecUnknown("")
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNPos) {
			isSuccess = glob.IsNPosNumLitExpr(leftFc)
			if isSuccess {
				return NewExecTrue("")
			} else {
				return NewExecUnknown("")
			}
		}
	}

	return NewExecUnknown("")
}

func (ver *Verifier) nPosElementGreaterThanLessThanOne(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	_ = "TODO"
	_ = stmt
	_ = state
	return NewExecUnknown("")
	// // 检查操作符是否是 ">"
	// if string(stmt.PropName) != glob.KeySymbolGreater {
	// 	return NewExecUnknown("")
	// }

	// if len(stmt.Params) != 2 {
	// 	return NewExecUnknown("")
	// }

	// // 检查左边是否是 N_pos 中的元素
	// leftInNPos := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.Params[0], ast.AtomObj(glob.KeywordNPos)}, stmt.Line)
	// verRet := ver.VerFactStmt(leftInNPos, state.GetNoMsg())
	// if verRet.IsErr() {
	// 	return verRet
	// }
	// if !verRet.IsTrue() {
	// 	// 左边不在 N_pos 中，返回 unknown
	// 	return NewExecUnknown("")
	// }

	// // 检查右边是否是数字字面量表达式
	// rightNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[1])
	// if err != nil {
	// 	return NewExecErr(err.Error())
	// }
	// if !ok {
	// 	// 右边不是数字字面量，返回 unknown
	// 	return NewExecUnknown("")
	// }

	// // 创建数字字面量 "1" 来比较
	// oneNumLitExpr := &glob.NumLitExpr{
	// 	IsPositive:  true,
	// 	Left:        nil,
	// 	OptOrNumber: "1",
	// 	Right:       nil,
	// }

	// // 检查右边是否 < 1
	// rightLessThanOne, err := glob.NumLitExprCompareOpt(rightNumLitExpr, oneNumLitExpr, "<")
	// if err != nil {
	// 	return NewExecErr(err.Error())
	// }
	// if !rightLessThanOne {
	// 	// 右边不小于 1，返回 unknown
	// 	return NewExecUnknown("")
	// }

	// // 左边是 N_pos 中的元素，右边 < 1，所以左边 > 右边
	// msg := fmt.Sprintf("%s is in N_pos and %s < 1, so %s > %s", stmt.Params[0], stmt.Params[1], stmt.Params[0], stmt.Params[1])
	// return ver.maybeAddSuccessMsg(state, stmt.String(), msg, NewExecTrue(""))
}
