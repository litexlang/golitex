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
)

// Each type of fact check takes the following steps: 1. check is valid 2. use built-in rules to check 3. use spec_mem to check 4. logic_mem to check 5. uni_mem to check

// factual chain: equal fact => specific fact => logical expr => uni fact
func (ver *Verifier) VerFact(stmt ast.FactStmt, state VerState) (bool, error) {
	if asSpecFact, ok := isEqualFact(stmt); ok {
		return ver.verEqual(asSpecFact, state)
	}

	if asSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
		return ver.verSpecFact(asSpecFact, state)
	}

	if asLogicExpr, ok := stmt.(*ast.LogicExprStmt); ok {
		return ver.verLogicExpr(asLogicExpr, state)
	}

	if asUniFact, ok := stmt.(*ast.UniFactStmt); ok {
		return ver.verUniFact(asUniFact, state)
	}

	return false, fmt.Errorf("unexpected fact statement: %v", stmt)
}
