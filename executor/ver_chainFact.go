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

func (ver *Verifier) verChainFactStmt(stmt *ast.ChainPureFact, state *VerState) ast.VerRet {
	if len(stmt.Objs) < 2 {
		return ast.NewErrVerRet(stmt).AddExtraInfo("chain fact must have at least 2 params")
	}

	for i := 0; i < len(stmt.Objs)-1; i++ {
		curFact := ast.NewPureSpecificFactStmt(true, stmt.PropNames[i], []ast.Obj{stmt.Objs[i], stmt.Objs[i+1]}, glob.BuiltinLine0)
		verRet := ver.VerFactStmt(curFact, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
		if verRet.IsUnknown() {
			return ast.NewUnknownVerRet(curFact)
		}
	}

	return ast.NewTrueVerRet(stmt, nil, "")
}
