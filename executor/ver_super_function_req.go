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

func (ver *Verifier) verSuperFunctionReq(fnObj *ast.FnObj, state *VerState) *glob.StmtRet {
	switch fnObj.FnHead.String() {
	case glob.KeywordUnion:
		return ver.verUnionReq(fnObj, state)
	case glob.KeywordIntersect:
		return ver.verIntersectReq(fnObj, state)
	default:
		return glob.ErrRet(fmt.Sprintf("unknown super function: %s", fnObj.FnHead))
	}
}

func (ver *Verifier) verUnionReq(fnObj *ast.FnObj, state *VerState) *glob.StmtRet {
	if len(fnObj.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("union expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	return glob.NewEmptyStmtTrue()
}

func (ver *Verifier) verIntersectReq(fnObj *ast.FnObj, state *VerState) *glob.StmtRet {
	if len(fnObj.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("intersect expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	return glob.NewEmptyStmtTrue()
}
