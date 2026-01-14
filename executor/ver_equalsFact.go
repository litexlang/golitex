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
	glob "golitex/glob"
)

func (ver *Verifier) verEqualsFactStmt(stmt *ast.EqualsFactStmt, state *VerState) *glob.VerRet {
	if len(stmt.Params) < 2 {
		return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{"equals fact must have at least 2 params"})
	}

	trueMsgs := []string{}

	for i := 1; i < len(stmt.Params); i++ {
		checked := false
		unknownRet := glob.NewEmptyVerRetUnknown()

		for j := i - 1; j >= 0; j-- {
			newFact := ast.NewEqualFact(stmt.Params[j], stmt.Params[i])
			verRet := ver.VerFactStmt(newFact, state)
			if verRet.IsErr() {
				newFact := ast.NewEqualFact(stmt.Params[i-1], stmt.Params[i])
				msgs := append(verRet.VerifyMsgs, fmt.Sprintf("%s\nis error", newFact.String()))
				return glob.NewVerMsg(glob.StmtRetTypeError, newFact.String(), glob.BuiltinLine0, msgs)
			}
			if verRet.IsTrue() {
				ret := ver.Env.NewFactWithCheckingNameDefined(newFact)
				if ret.IsErr() {
					return glob.NewVerMsg(glob.StmtRetTypeError, newFact.String(), glob.BuiltinLine0, []string{ret.String()})
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
			msgs := append(unknownRet.VerifyMsgs, fmt.Sprintf("%s\nis unknown", newFact.String()))
			return glob.NewVerMsg(glob.StmtRetTypeUnknown, newFact.String(), glob.BuiltinLine0, msgs)
		}
	}
	if state.WithMsg {
		return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, trueMsgs)
	}
	return glob.NewEmptyVerRetTrue()
}
