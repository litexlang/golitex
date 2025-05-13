// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) ParamInParamSets(stmt *ast.DefHeader) ([]ast.SpecFactStmt, error) {
	ret := []ast.SpecFactStmt{}

	for i, param := range stmt.Params {
		paramAsAtom := ast.NewFcAtomWithName(param)
		specFact := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{paramAsAtom, stmt.SetParams[i]})
		ret = append(ret, *specFact)
	}

	return ret, nil
}
