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

import ast "golitex/ast"

func (ver *Verifier) verIntensionalSetStmt(stmt *ast.IntensionalSetStmt, state VerState) (bool, error) {
	leftUniFact, rightUniFact, err := stmt.ToEquivalentUniFacts()
	if err != nil {
		return false, err
	}

	ok, err := ver.verUniFact(leftUniFact, state)
	if err != nil || !ok {
		return false, err
	}

	ok, err = ver.verUniFact(rightUniFact, state)
	if err != nil || !ok {
		return false, err
	}

	return true, nil
}
