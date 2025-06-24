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

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// left dom >= right dom
// left dom + left then + right dom => right then
func (ver *Verifier) leftDomLeadToRightDom_RightDomLeadsToRightThen(funcName ast.Fc, leftT *ast.FnTemplateStmt, rightT *ast.FnTemplateStmt, state VerState) (bool, error) {
	if len(leftT.Params) != len(rightT.Params) {
		return false, fmt.Errorf("the number of parameters of the left function definition is not equal to the number of parameters of the right function definition")
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range rightT.Params {
		uniMap[param] = ast.NewFcAtomWithName(leftT.Params[i])
	}

	instantiatedSetParams, instantiatedDomFacts, instantiatedThenFacts, instantiatedRetSet, err := rightT.InstantiateFnTWithoutChangingTName(uniMap)
	if err != nil {
		return false, err
	}

	inRightSetParamFacts := []ast.FactStmt{}
	for i, setParam := range instantiatedSetParams {
		inRightSetParamFacts = append(inRightSetParamFacts, ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{ast.NewFcAtomWithName(leftT.Params[i]), setParam}))
	}

	fcFnParams := []ast.Fc{}
	for _, param := range leftT.Params {
		fcFnParams = append(fcFnParams, ast.NewFcAtomWithName(param))
	}
	fcFn := ast.NewFcFn(funcName, fcFnParams)

	fcFnInLeftRetSet := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{fcFn, leftT.RetSet})

	// left dom => right dom
	leftDomToRightDomUniFact := ast.NewUniFact(leftT.Params, leftT.ParamSets, leftT.DomFacts, append(inRightSetParamFacts, instantiatedThenFacts...))

	ok, err := ver.VerFactStmt(leftDomToRightDomUniFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	// left dom + left in set params + left then + right dom + right in set params => right then
	leftDomToRightDomFacts := []ast.FactStmt{}
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, leftT.DomFacts...)
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, fcFnInLeftRetSet)
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, leftT.ThenFacts...)
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, inRightSetParamFacts...)
	leftDomToRightDomFacts = append(leftDomToRightDomFacts, instantiatedDomFacts...)

	rightThenFacts := []ast.FactStmt{}
	rightThenFacts = append(rightThenFacts, ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{fcFn, instantiatedRetSet}))
	rightThenFacts = append(rightThenFacts, instantiatedThenFacts...)

	leftDom_leftThen_rightDom_rightThen_uniFact := ast.NewUniFact(leftT.Params, leftT.ParamSets, leftDomToRightDomFacts, rightThenFacts)

	if ok, err := ver.VerFactStmt(leftDom_leftThen_rightDom_rightThen_uniFact, state); err != nil || !ok {
		return false, err
	}

	return true, nil
}
