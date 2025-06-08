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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex discord server: https://discord.gg/uvrHM7eS
// Litex zulip chat: https://litex.zulipchat.com/

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
	uniSetParams := defOfFn.DefHeader.SetParams
	uniFactDomFacts := defOfFn.DomFacts

	leftParam := ast.NewFcAtomWithName(uniFactParams[0])
	rightParam := ast.NewFcAtomWithName(uniFactParams[1])

	fnName := ast.NewFcAtomWithName(defOfFn.DefHeader.Name)

	leftFnParamOfEqualFact := ast.NewFcFn(fnName, []ast.Fc{leftParam, rightParam})
	rightFnParamOfEqualFact := ast.NewFcFn(fnName, []ast.Fc{rightParam, leftParam})

	equalFact := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeySymbolEqual), []ast.Fc{leftFnParamOfEqualFact, rightFnParamOfEqualFact})

	uniFact := ast.NewUniFact(
		uniFactParams,
		uniSetParams,
		uniFactDomFacts,
		[]ast.FactStmt{equalFact},
		ast.EmptyIffFacts,
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
