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

package data_cleaner

import (
	"fmt"
	ast "golitex/ast"
	parser "golitex/parser"
)

type CleanData struct {
	Assumptions string
	ClaimData   CleanClaimData
}

type CleanClaimData struct {
	ClaimAssumption string
	ClaimResult     string
	Proofs          string
}

func CleanStmt(code string) (*CleanData, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, err
	}

	if len(topStmtSlice) != 1 {
		return nil, fmt.Errorf("expect exactly one statement")
	}

	switch topStmtSlice[0].(type) {
	case *ast.ClaimProveStmt:
		return cleanClaimProveStmt(topStmtSlice[0].(*ast.ClaimProveStmt))
	case *ast.ProveStmt:
		return cleanProveStmt(topStmtSlice[0].(*ast.ProveStmt))
	default:
		return nil, fmt.Errorf("expect claim statement")
	}
}

func cleanClaimProveStmt(claimProveStmt *ast.ClaimProveStmt) (*CleanData, error) {
}

func cleanProveStmt(proveStmt *ast.ProveStmt) (*CleanData, error) {
	return proveStmt.String(), nil
}
