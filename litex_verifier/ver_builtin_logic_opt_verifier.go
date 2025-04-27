// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

func (ver *Verifier) btLogicOptBtRule(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.btLogicUnaryOptBtRule(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	ok, err = ver.btLogicInfixOptBtRule(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}

func (ver *Verifier) btLogicUnaryOptBtRule(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.PropName.PkgName != glob.BuiltinUnaryPkgName {
		return false, nil
	}
	_ = state

	// TODO 实现单一的builtin unary rule
	return false, nil
}

func (ver *Verifier) btLogicInfixOptBtRule(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.PropName.PkgName != "" {
		return false, nil
	}

	if !glob.IsKeySymbolRelaProp(stmt.PropName.Name) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	leftNumLitExpr, ok, err := ast.IsFcBuiltinNumLitExpr(stmt.Params[0])
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightNumLitExpr, ok, err := ast.IsFcBuiltinNumLitExpr(stmt.Params[1])
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = glob.NumLitExprLogicOpt(leftNumLitExpr, rightNumLitExpr, stmt.PropName.Name)

	if err != nil {
		return false, err
	}
	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "builtin rules")
		} else {
			ver.successNoMsg()
		}
		return true, nil
	}
	return false, nil
}
