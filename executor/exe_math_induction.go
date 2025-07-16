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

func (exec *Executor) mathInductionFact_BuiltinRules(stmt *ast.ProveByMathInductionStmt) (glob.ExecState, error) {
	isTrue := false
	exec.newEnv(exec.env)
	var propNameZeroFact ast.FactStmt
	var nToNAddOneFact ast.FactStmt
	var resultingFact *ast.UniFactStmt

	defer func() {
		exec.deleteEnvAndRetainMsg()
		if isTrue {
			exec.env.Msgs = append(exec.env.Msgs, fmt.Sprintf("by %s\n%s\nis true", glob.KeywordProveByMathInduction, resultingFact))
			exec.knowStmt(ast.NewKnowStmt([]ast.FactStmt{resultingFact}))
		}
	}()

	ver := verifier.NewVerifier(exec.env)

	startSpecFactParams := glob.CopySlice(stmt.Fact.Params)
	startSpecFactParams[stmt.ParamIndex] = ast.FcAtom("n") // 这个n可能有点不好，因为n可能和其他的参数重名

	startSpecFact := ast.NewSpecFactStmt(
		stmt.Fact.TypeEnum,
		stmt.Fact.PropName,
		startSpecFactParams,
	)

	domFacts := make([]ast.FactStmt, 2)
	domFacts[0] = ast.NewSpecFactStmt(
		ast.TruePure,
		ast.FcAtom(glob.KeySymbolLargerEqual),
		[]ast.Fc{ast.FcAtom("n"), ast.FcAtom(fmt.Sprintf("%d", stmt.Start))},
	)

	domFacts[1] = startSpecFact

	thenFacts := make([]ast.FactStmt, 1)
	thenFacts[0] = ast.NewSpecFactStmt(
		ast.TruePure,
		stmt.Fact.PropName,
		[]ast.Fc{ast.NewFcFn(ast.FcAtom(glob.KeySymbolPlus), []ast.Fc{ast.FcAtom("n"), ast.FcAtom("1")})},
	)

	paramInSetsFacts := make([]ast.FactStmt, 1)
	paramInSetsFacts[0] = ast.NewInFact("n", ast.FcAtom(glob.KeywordNatural))
	paramSets := make([]ast.Fc, 1)
	paramSets[0] = ast.FcAtom(glob.KeywordNatural)

	nToNAddOneFact = ast.NewUniFact(
		[]string{"n"},
		paramSets,
		domFacts,
		thenFacts,
	)

	ok, err := ver.VerFactStmt(propNameZeroFact, verifier.Round0NoMsg)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if !ok {
		return glob.ExecState_Error, nil
	}

	ok, err = ver.VerFactStmt(nToNAddOneFact, verifier.Round0NoMsg)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if !ok {
		return glob.ExecState_Error, nil
	}

	isTrue = true

	resultingFact = ast.NewUniFact(
		[]string{"n"},
		paramSets,
		[]ast.FactStmt{ast.NewSpecFactStmt(
			ast.TruePure,
			ast.FcAtom(glob.KeySymbolLargerEqual),
			[]ast.Fc{ast.FcAtom("n"), ast.FcAtom(fmt.Sprintf("%d", stmt.Start))},
		)},
		[]ast.FactStmt{startSpecFact},
	)

	return glob.ExecState_True, nil
}
