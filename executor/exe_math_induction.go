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

// func (exec *Executor) proveByMathInduction(stmt *ast.ProveByMathInductionStmt) (glob.ExecState, error) {
// 	isTrue := false
// 	exec.NewEnv(exec.env)
// 	var resultingFact *ast.UniFactStmt

// 	defer func() {
// 		exec.deleteEnvAndRetainMsg()
// 		if isTrue {
// 			exec.env.Msgs = append(exec.env.Msgs, fmt.Sprintf("by %s\n%s\nis true", glob.KeywordProveByMathInduction, resultingFact))
// 		}
// 	}()

// 	ver := verifier.NewVerifier(exec.env)

// 	freeVarStr := exec.env.GenerateUndeclaredRandomName()

// 	startSpecFactParams := glob.CopySlice(stmt.Fact.Params)
// 	startSpecFactParams[stmt.ParamIndex] = ast.FcAtom(freeVarStr)

// 	specFactWithFreeVar := ast.NewSpecFactStmt(
// 		stmt.Fact.TypeEnum,
// 		stmt.Fact.PropName,
// 		startSpecFactParams,
// 	)

// 	domFacts := make([]ast.FactStmt, 2)
// 	domFacts[0] = ast.NewSpecFactStmt(
// 		ast.TruePure,
// 		ast.FcAtom(glob.KeySymbolLargerEqual),
// 		[]ast.Fc{ast.FcAtom(freeVarStr), ast.FcAtom(fmt.Sprintf("%d", stmt.Start))},
// 	)

// 	domFacts[1] = specFactWithFreeVar

// 	startSpecFactParamsPlusOne := glob.CopySlice(stmt.Fact.Params)
// 	startSpecFactParamsPlusOne[stmt.ParamIndex] = ast.NewFcFn(ast.FcAtom(glob.KeySymbolPlus), []ast.Fc{ast.FcAtom(freeVarStr), ast.FcAtom("1")})
// 	specFactWithFreeVarPlusOne := ast.NewSpecFactStmt(
// 		stmt.Fact.TypeEnum,
// 		stmt.Fact.PropName,
// 		startSpecFactParamsPlusOne,
// 	)

// 	thenFacts := make([]ast.FactStmt, 1)
// 	thenFacts[0] = specFactWithFreeVarPlusOne

// 	paramInSetsFacts := make([]ast.FactStmt, 1)
// 	paramInSetsFacts[0] = ast.NewInFact(freeVarStr, ast.FcAtom(glob.KeywordNatural))
// 	paramSets := make([]ast.Fc, 1)
// 	paramSets[0] = ast.FcAtom(glob.KeywordNatural)

// 	nToNAddOneFact := ast.NewUniFact(
// 		[]string{freeVarStr},
// 		paramSets,
// 		domFacts,
// 		thenFacts,
// 	)

// 	specFactParamsStart := glob.CopySlice(stmt.Fact.Params)
// 	specFactParamsStart[stmt.ParamIndex] = ast.FcAtom(fmt.Sprintf("%d", stmt.Start))

// 	propNameZeroFact := ast.NewSpecFactStmt(
// 		stmt.Fact.TypeEnum,
// 		stmt.Fact.PropName,
// 		specFactParamsStart,
// 	)

// 	ok, err := ver.VerFactStmt(propNameZeroFact, verifier.Round0NoMsg)
// 	if err != nil {
// 		return glob.ExecState_Error, err
// 	}
// 	if !ok {
// 		return glob.ExecState_Error, nil
// 	}

// 	ok, err = ver.VerFactStmt(nToNAddOneFact, verifier.Round0NoMsg)
// 	if err != nil {
// 		return glob.ExecState_Error, err
// 	}
// 	if !ok {
// 		return glob.ExecState_Error, nil
// 	}

// 	isTrue = true

// 	if isSpecFact_ParamIndex1Is0(domFacts[0]) {
// 		resultingFact = ast.NewUniFact(
// 			[]string{freeVarStr},
// 			paramSets,
// 			[]ast.FactStmt{},
// 			[]ast.FactStmt{domFacts[1]},
// 		)
// 	} else {
// 		resultingFact = ast.NewUniFact(
// 			[]string{freeVarStr},
// 			paramSets,
// 			[]ast.FactStmt{domFacts[0]},
// 			[]ast.FactStmt{domFacts[1]},
// 		)
// 	}

// 	err = exec.env.Parent.NewFact(resultingFact)
// 	if err != nil {
// 		return glob.ExecState_Error, err
// 	}

// 	return glob.ExecState_True, nil
// }

// func isSpecFact_ParamIndex1Is0(fact ast.FactStmt) bool {
// 	asSpecFact, ok := fact.(*ast.SpecFactStmt)
// 	if !ok {
// 		return false
// 	}
// 	return asSpecFact.Params[1] == ast.FcAtom("0")
// }
