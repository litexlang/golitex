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
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	verifier "golitex/verifier"
)

func (exec *Executor) mathInductionFact_BuiltinRules(stmt *ast.SpecFactStmt) (bool, error) {
	ver := verifier.NewVerifier(exec.env)

	if len(stmt.Params) != 1 {
		return false, fmt.Errorf("math induction fact %s should have exactly one parameter, got: %d", stmt.String(), len(stmt.Params))
	}

	propNameAsAtom, ok := stmt.Params[0].(ast.FcAtom)
	if !ok {
		return false, fmt.Errorf("math induction fact %s should have a prop name as parameter, got: %s", stmt.String(), stmt.Params[0])
	}

	_, ok = exec.env.GetPropDef(propNameAsAtom)
	if !ok {
		return false, fmt.Errorf("math induction fact %s should have a prop name that is defined, got: %s", stmt.String(), propNameAsAtom)
	}

	// propName(0) is true
	propNameZeroFact := ast.NewSpecFactStmt(ast.TruePure, propNameAsAtom, []ast.Fc{ast.FcAtom("0")})

	// propName(n) => propName(n+1)
	params := []string{"n"}

	domFacts := make([]ast.FactStmt, 1)
	domFacts[0] = ast.NewSpecFactStmt(
		ast.TruePure,
		propNameAsAtom,
		[]ast.Fc{ast.FcAtom("n")},
	)
	thenFacts := make([]ast.FactStmt, 1)
	thenFacts[0] = ast.NewSpecFactStmt(
		ast.TruePure,
		propNameAsAtom,
		[]ast.Fc{ast.NewFcFn(ast.FcAtom(glob.KeySymbolPlus), []ast.Fc{ast.FcAtom("n"), ast.FcAtom("1")})},
	)

	paramInSetsFacts := make([]ast.FactStmt, 1)
	paramInSetsFacts[0] = ast.NewInFact("n", ast.FcAtom(glob.KeywordNatural))
	paramSets := make([]ast.Fc, 1)
	paramSets[0] = ast.FcAtom(glob.KeywordNatural)

	nToNAddOneFact := ast.NewUniFact(
		params,
		paramSets,
		domFacts,
		thenFacts,
	)

	ok, err := ver.VerFactStmt(propNameZeroFact, verifier.Round0Msg)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = ver.VerFactStmt(nToNAddOneFact, verifier.Round0Msg)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}
