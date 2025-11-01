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
	cmp "golitex/cmp"
)

func (ver *Verifier) verByReplaceFcInSpecFactWithValue(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	replaced, newStmt := ver.env.ReplaceFcInSpecFactWithValue(stmt)
	if replaced {
		verRet := ver.verTrueEqualFactMainLogic(newStmt, state, true)
		if verRet.IsErr() {
			return NewVerErr("failed to verify true equal fact: " + verRet.String())
		}

		if verRet.IsTrue() {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
			}

			values := []ast.Fc{}
			if cmp.IsNumLitFc(newStmt.Params[0]) {
				values = append(values, newStmt.Params[0])
			} else {
				values = append(values, nil)
			}

			if cmp.IsNumLitFc(newStmt.Params[1]) {
				values = append(values, newStmt.Params[1])
			} else {
				values = append(values, nil)
			}

			if values[0] == nil && values[1] == nil {
				return NewVerTrue(fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
			} else {
				return NewVerTrueWithValues(fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()), values)
			}
		}
	}

	return NewVerUnknown(fmt.Sprintf("%s is not equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
}

func (ver *Verifier) verByReplaceFcInSpecFactWithValueAndCompute(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	replaced, newStmt := ver.env.ReplaceFcInSpecFactWithValue(stmt)

	if replaced {
		verRet := ver.verTrueEqualFactMainLogic(newStmt, state, true)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values and computing", stmt.String(), newStmt.String()))
			}
			return NewVerTrue("")
		}
	}

	return NewVerUnknown("")
}
