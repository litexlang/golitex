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

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) commutativeFnByDef(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if len(stmt.Params) != 1 {
		return false, fmt.Errorf("commutative fn fact %s should have exactly one parameter, got: %d", stmt.String(), len(stmt.Params))
	}

	defOfFn, ok := ver.env.GetFnDef(stmt.Params[0])
	if !ok {
		return false, fmt.Errorf("commutative fn fact %s should have a function definition, but got: %s", stmt.String(), stmt.Params[0].String())
	}

	uniFactParams := defOfFn.DefHeader.Params
	uniFactParamInSetsFacts := defOfFn.DefHeader.ParamInSetsFacts
	uniFactDomFacts := defOfFn.DomFacts

	leftParam := ast.NewFcAtomWithName(uniFactParams[0])
	rightParam := ast.NewFcAtomWithName(uniFactParams[1])

	fnName := ast.NewFcAtomWithName(defOfFn.DefHeader.Name)

	leftFnParamOfEqualFact := ast.NewFcFn(fnName, []ast.Fc{leftParam, rightParam}, nil)
	rightFnParamOfEqualFact := ast.NewFcFn(fnName, []ast.Fc{rightParam, leftParam}, nil)

	equalFact := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeySymbolEqual), []ast.Fc{leftFnParamOfEqualFact, rightFnParamOfEqualFact})

	uniFact := ast.NewUniFactStmtWithSetReqInDom(
		uniFactParams,
		uniFactDomFacts,
		[]ast.FactStmt{equalFact},
		ast.EmptyIffFacts,
		uniFactParamInSetsFacts,
	)

	ok, err := ver.FactStmt(uniFact, state.addRound())
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}
