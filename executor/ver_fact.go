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

func (ver *Verifier) VerFactStmt(stmt ast.FactStmt, state *VerState) *glob.GlobRet {
	switch asStmt := stmt.(type) {
	case *ast.SpecFactStmt:
		if ast.IsTrueSpecFactWithPropName(asStmt, glob.KeySymbolEqual) {
			return ver.verTrueEqualFactAndCheckFnReq(asStmt, state)
		} else {
			return ver.verSpecFactNotInFormOfTrueEqualAndCheckFnReq(asStmt, state)
		}
	case *ast.OrStmt:
		return ver.verOrStmt(asStmt, state)
	case *ast.UniFactStmt:
		return ver.verUniFact(asStmt, state)
	case *ast.UniFactWithIffStmt:
		return ver.verUniFactWithIff(asStmt, state)
	case *ast.EqualsFactStmt:
		return ver.verEqualsFactStmt(asStmt, state)
	default:
		return glob.NewGlobErr(fmt.Sprintf("unexpected fact statement: %s", asStmt))
	}
}
