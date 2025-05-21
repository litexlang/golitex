// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (ver *Verifier) verEqual(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !isValidEqualFact(stmt) {
		return false, fmt.Errorf("invalid equal fact: %v", stmt)
	}

	return ver.verEqual_FnIsCommutativeOrAssociative(stmt)
}

func (ver *Verifier) verEqual_FnIsCommutativeOrAssociative(stmt *ast.SpecFactStmt) (bool, error) {
	return ver.verEqualCommutatively(stmt)
}

func isValidEqualFact(stmt *ast.SpecFactStmt) bool {
	return len(stmt.Params) == 2 && stmt.PropName.Name == glob.KeySymbolEqual
}

func (ver *Verifier) verEqualCommutatively(stmt *ast.SpecFactStmt) (bool, error) {
	stmtWithReversedParamOrder, err := stmt.ReverseSpecFactParamsOrder()
	if err != nil {
		return false, err
	}

	statements := []*ast.SpecFactStmt{stmt, stmtWithReversedParamOrder}

	for _, s := range statements {
		ok, err := verEqualBuiltin(s)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verEqualLeftToRight(stmt *ast.SpecFactStmt) (bool, error) {
	// TODO: 在这里处理 stmt 的 fn 是 可交换，可结合的情况
	if ok, err := verEqualBuiltin(stmt); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	return false, nil
}

func verEqualBuiltin(stmt *ast.SpecFactStmt) (bool, error) {
	ok, err := cmp.CmpFcRule(stmt.Params[0], stmt.Params[1])
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}
