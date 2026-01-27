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
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) VerTrueEqualFactAndCheckFnReq2(stmt ast.SpecificFactStmt, state *VerState) *glob.VerRet {
	if !state.ReqOk {
		if verRet := ver.checkFnsReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		state.UpdateReqOkToTrue()
	}

	if verRet := ver.verByReplaceObjInSpecFactWithValue(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	if verRet := ver.verTrueEqualFactOldMainLogic(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verTrueEqualFactPreProcess(stmt ast.SpecificFactStmt, state *VerState) *glob.VerRet {
	panic("not implemented")
}

func (ver *Verifier) verTrueEqualFactMainLogic(stmt ast.SpecificFactStmt, state *VerState) *glob.VerRet {
	panic("not implemented")
}

func (ver *Verifier) verTrueEqualFactPostProcess(stmt ast.SpecificFactStmt, state *VerState) *glob.VerRet {
	panic("not implemented")
}
