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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	ast "golitex/ast"
)

func (ver *Verifier) verEnumStmt(stmt *ast.EnumStmt, state VerState) (bool, error) {
	forallItemInSetEqualToOneOfGivenItems, pairwiseNotEqualFacts, itemsInSetFacts := ast.TransformEnumToUniFact(stmt.EnumName, stmt.EnumValues)

	ok, err := ver.VerFactStmt(forallItemInSetEqualToOneOfGivenItems, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	for _, domFact := range pairwiseNotEqualFacts {
		ok, err := ver.VerFactStmt(domFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	for _, equalFact := range itemsInSetFacts {
		ok, err := ver.VerFactStmt(equalFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
