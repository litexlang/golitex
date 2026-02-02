// Copyright Jiachen Shen.
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

func (ver *Verifier) verEqualsFactStmt(stmt *ast.EqualsFactStmt, state *VerState) ast.VerRet {
	if len(stmt.Params) < 2 {
		return ast.NewErrVerRet(stmt).AddExtraInfo("equals fact must have at least 2 params")
	}

	trueMsgs := []string{}

	for i := 1; i < len(stmt.Params); i++ {
		checked := false
		var unknownRet ast.VerRet = ast.NewEmptyUnknownVerRet()

		for j := i - 1; j >= 0; j-- {
			newFact := ast.NewEqualFact(stmt.Params[j], stmt.Params[i])
			verRet := ver.VerFactStmt(newFact, state)
			if verRet.IsErr() {
				newFact := ast.NewEqualFact(stmt.Params[i-1], stmt.Params[i])
				msgs := append(verRet.GetExtraInfos(), fmt.Sprintf("%s\nis error", newFact.String()))
				return ast.NewErrVerRet(newFact).AddExtraInfos(msgs)
			}
			if verRet.IsTrue() {
				ret := ver.Env.NewFactWithCheckingNameDefined(newFact)
				if ret.IsErr() {
					return ast.NewErrVerRet(newFact).AddExtraInfo(ret.String())
				}
				checked = true
				trueMsgs = append(trueMsgs, verRet.String())
				break
			}

			if j == i-1 {
				unknownRet = verRet
			}
		}

		if !checked {
			newFact := ast.NewEqualFact(stmt.Params[i-1], stmt.Params[i])
			msgs := append(unknownRet.GetExtraInfos(), fmt.Sprintf("%s\nis unknown", newFact.String()))
			return ast.NewUnknownVerRet(newFact).AddExtraInfos(msgs)
		}
	}
	if state.WithMsg {
		return ast.NewTrueVerRet(stmt, nil, "").AddExtraInfos(trueMsgs)
	}
	return ast.NewTrueVerRet(stmt, nil, "")
}
