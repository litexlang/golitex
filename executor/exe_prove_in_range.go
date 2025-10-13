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
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) proveInRangeStmt(stmt *ast.ProveInRangeStmt) (glob.ExecState, error) {
	// 变成str
	// startStr := strconv.FormatInt(stmt.Start, 10)
	// endStr := strconv.FormatInt(stmt.End, 10)

	// forallXInIntensionalSetTheyAreFromStartToEnd := ast.NewUniFact([]string{stmt.Param}, []ast.Fc{stmt.IntensionalSet}, []ast.FactStmt{}, []ast.FactStmt{ast.NewInFact(stmt.Param, stmt.IntensionalSet)}, stmt.Line)
	panic("")
}
