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

func (ver *Verifier) verNumberLogicRelaOpt_BuiltinRules(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if !stmt.IsTrue() {
		return NewVerUnknown("")
	}

	verRet := ver.btNumberInfixCompareProp(stmt, state)
	return verRet
}

func (ver *Verifier) btNumberInfixCompareProp(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if !glob.IsBuiltinNumberInfixRelaProp(string(stmt.PropName)) {
		return NewVerUnknown("")
	}

	if len(stmt.Params) != 2 {
		return NewVerErr(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	leftNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return NewVerErr(err.Error())
	}
	if !ok {
		return NewVerUnknown("")
	}

	rightNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[1])
	if err != nil {
		return NewVerErr(err.Error())
	}
	if !ok {
		return NewVerUnknown("")
	}

	ok, err = glob.NumLitExprCompareOpt(leftNumLitExpr, rightNumLitExpr, string(stmt.PropName))

	if err != nil {
		return NewVerErr(err.Error())
	}
	if ok {
		if state.WithMsg {
			ver.successWithMsg(stmt.String(), "builtin rules")
		}
		return NewVerTrue("")
	}

	return NewVerUnknown("")
}

func (ver *Verifier) btLitNumInNatOrIntOrRatOrRealOrComplex(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if stmt.PropName != glob.KeywordIn {
		return false, nil
	}

	isSuccess := false
	defer func() {
		if isSuccess {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), "builtin rules")
			}
		}
	}()

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	leftFc, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return false, err
	}
	if ok {
		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordInteger) {
			isSuccess = glob.IsIntegerNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordComplex) {
			isSuccess = glob.IsComplexNumLitExpr(leftFc)
			return isSuccess, nil
		}

		if ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordNPos) {
			isSuccess = glob.IsNPosNumLitExpr(leftFc)
			return isSuccess, nil
		}
	}

	return false, nil
}
