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
	glob "golitex/glob"
)

func (ver *Verifier) verEqual(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !isValidEqualFact(stmt) {
		return false, fmt.Errorf("invalid equal fact: %v", stmt)
	}

	return verEqualCommutatively(stmt)
}

func isValidEqualFact(stmt *ast.SpecFactStmt) bool {
	return len(stmt.Params) == 2 && stmt.PropName.Name == glob.KeySymbolEqual
}

func verEqualCommutatively(stmt *ast.SpecFactStmt) (bool, error) {
	if ok, err := verEqualLeftToRight(stmt); ok {
		return true, nil
	} else if err != nil {
		return false, err
	}

	newStmt := stmt.ReverseSpecFactParamsOrder()
	if ok, err := verEqualLeftToRight(newStmt); ok {
		return true, nil
	} else if err != nil {
		return false, err
	}

	return false, nil
}

func verEqualLeftToRight(stmt *ast.SpecFactStmt) (bool, error) {
	if ok, err := verEqualBuiltin(stmt); ok {
		return true, nil
	} else if err != nil {
		return false, err
	}

	return true, nil
}

func verEqualBuiltin(stmt *ast.SpecFactStmt) (bool, error) {
	return false, nil
}
