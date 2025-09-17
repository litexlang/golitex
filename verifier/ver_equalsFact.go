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

package litex_verifier

import ast "golitex/ast"

func (ver *Verifier) verEqualsFactStmt(stmt *ast.EqualsFactStmt, state *VerState) (bool, error) {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ok, err := ver.VerFactStmt(equalFact, state)
		if err != nil {
			return false, err
		} else if !ok {
			return false, nil
		}
	}
	return true, nil
}

// func (ver *Verifier) verEqualsFactStmt(stmt *ast.EqualsFactStmt, state *VerState) (bool, error) {
// 	if len(stmt.Params) < 2 {
// 		return false, fmt.Errorf("equals fact must have at least 2 params")
// 	}

// 	for i := range len(stmt.Params) - 1 {
// 		checked := false
// 		for j := i - 1; j >= 0; j-- {
// 			newFact := ast.NewEqualFact(stmt.Params[i], stmt.Params[j])
// 			ok, err := ver.VerFactStmt(newFact, state)
// 			if err != nil {
// 				return false, err
// 			}
// 			if ok {
// 				checked = true
// 				break
// 			}
// 		}

// 		if !checked {
// 			return false, nil
// 		}
// 	}
// 	return true, nil
// }
