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

func (exec *Executor) mathInductionFact_BuiltinRules(stmt *ast.ProveByMathInductionStmt) (bool, error) {
	ver := verifier.NewVerifier(exec.env)

	propNameAsAtom := stmt.PropName

	_, ok := exec.env.GetPropDef(propNameAsAtom)
	if !ok {
		_, ok := exec.env.GetExistPropDef(propNameAsAtom)
		if !ok {
			return false, fmt.Errorf("math induction fact %s should have a prop name that is defined, got: %s", stmt.String(), propNameAsAtom)
		}
	}

	// propName(start) is true
	propNameZeroFact := ast.NewSpecFactStmt(ast.TruePure, propNameAsAtom, []ast.Fc{stmt.Start})

	// propName(n) => propName(n+1)
	params := []string{"n"}

	domFacts := make([]ast.FactStmt, 2)
	domFacts[0] = ast.NewSpecFactStmt(
		ast.TruePure,
		ast.FcAtom(glob.KeySymbolLargerEqual),
		[]ast.Fc{ast.FcAtom("n"), stmt.Start},
	)

	domFacts[1] = ast.NewSpecFactStmt(
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
