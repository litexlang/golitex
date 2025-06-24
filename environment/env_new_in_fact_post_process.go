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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (e *Env) inFactPostProcess(fact *ast.SpecFactStmt) error {
	if len(fact.Params) != 2 {
		return fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact.String())
	}

	if isTemplate, err := e.inFactPostProcess_InFnTemplate(fact); isTemplate {
		return err
	}

	if ast.IsFcWithFcFnHeadWithName(fact.Params[1], glob.KeywordFn) {
		templateStmt, err := ast.FnFcToFnTemplateStmt(fact.Params[1])
		if err != nil {
			return err
		}

		ok, err := e.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(fact.Params[0], templateStmt)
		if err != nil {
			return err
		}

		if !ok {
			return fmt.Errorf("failed to satisfy the function template of %s", fact.Params[0].String())
		}
	}

	return nil
}

func (e *Env) inFactPostProcess_InFnTemplate(fact *ast.SpecFactStmt) (bool, error) {
	templateName, ok := fact.Params[1].(*ast.FcAtom)
	if !ok {
		return false, nil
	}

	curInTemplate, ok := e.GetFnTemplateDef(templateName)
	if !ok {
		return false, nil
	}

	return e.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(fact.Params[0], &curInTemplate.FnTemplateStmt)
}

func (e *Env) FcSatisfy_FreeTemplateFact_Store_DeriveFacts(fc ast.Fc, fnTemplate *ast.FnTemplateStmt) (bool, error) {
	instantiatedFnTStmt, err := fnTemplate.InstantiateByFnName_WithTemplateNameGivenFc(fc)
	if err != nil {
		return false, err
	}

	err = e.StoreFnSatisfyFnTemplateFact(fc, instantiatedFnTStmt)
	if err != nil {
		return false, err
	}

	derivedFact := instantiatedFnTStmt.DeriveUniFact(fc)
	err = e.NewFact(derivedFact)
	if err != nil {
		return false, err
	}

	return true, nil
}
