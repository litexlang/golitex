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
)

func (ver *Verifier) verByReplaceFcInSpecFactWithValue(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	var ok bool
	var err error
	replaced, newStmt := ver.env.ReplaceFcInSpecFactWithValue(stmt)
	if replaced {
		ok, err = ver.verTrueEqualFactMainLogic(newStmt, state, true)
		if err != nil {
			return false, err
		}

		if ok {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
			}
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verByReplaceFcInSpecFactWithValueAndCompute(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	var ok bool
	var err error
	replaced, newStmt := ver.env.ReplaceFcInSpecFactWithValue(stmt)

	if replaced {
		ok, err = ver.verTrueEqualFactMainLogic(newStmt, state, true)
		if err != nil {
			return false, err
		}
		if ok {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values and computing", stmt.String(), newStmt.String()))
			}
			return true, nil
		}
	}

	return false, nil
}
