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
		return fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact)
	}

	if def, ok := e.isSetFnRetValue(fact.Params[1]); ok {
		return e.inFactPostProcess_InSetFnRetValue(fact, def)
	}

	if isTemplate, err := e.inFactPostProcess_InFnTemplate(fact); isTemplate || err != nil {
		return err
	}

	if fnFn, ok := fact.Params[1].(*ast.FcFn); ok && ast.IsFnTemplate_FcFn(fnFn) {
		fnTNoName, err := fnFn.FnTFc_ToFnTNoName()
		if err != nil {
			return err
		}
		err = e.InsertFnInFnTT(fact.Params[0], fnFn, fnTNoName)
		if err != nil {
			return err
		}

		return nil
	}

	if setDefinedByReplacement, ok := fact.Params[1].(*ast.FcFn); ok && ast.IsFcAtomAndEqualToStr(setDefinedByReplacement.FnHead, glob.KeywordSetDefinedByReplacement) {
		return e.in_setDefinedByReplacement_postProcess(setDefinedByReplacement)
	}

	return nil
}

func (e *Env) inFactPostProcess_InSetFnRetValue(fact *ast.SpecFactStmt, def *ast.HaveSetFnStmt) error {
	inFactRightParamAsFcFnPt, ok := fact.Params[1].(*ast.FcFn)
	if !ok {
		return fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact)
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range def.DefHeader.Params {
		uniMap[param] = inFactRightParamAsFcFnPt.Params[i]
	}

	defToIntensionalSetStmt := def.ToIntensionalSetStmt()
	instantiated, err := defToIntensionalSetStmt.Instantiate(uniMap)
	if err != nil {
		return err
	}

	err = e.NewFact(instantiated)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) in_setDefinedByReplacement_postProcess(setDefinedByReplacement *ast.FcFn) error {
	uniFact := ast.ForallYInSetDefinedByReplacementThereIsXSTProp_X_YIsTrue(setDefinedByReplacement)
	err := e.NewFact(uniFact)
	if err != nil {
		return err
	}

	// forall x set_defined_by_replacement(A, B, P), x is in B
	forallXInSetDefinedByReplacement_ItIsInB := ast.NewUniFact([]string{"x"}, []ast.Fc{setDefinedByReplacement}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{ast.FcAtom("x"), setDefinedByReplacement.Params[1]})})
	err = e.NewFact(forallXInSetDefinedByReplacement_ItIsInB)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) SetEqualToSetDefinedByReplacement_PostProcess(setAtom ast.FcAtom, setDefinedByReplacement *ast.FcFn) error {
	uniFact := ast.ForallYInSetDefinedByReplacementThereIsXSTProp_X_YIsTrue(setDefinedByReplacement)
	uniFact.ParamSets[0] = setAtom
	err := e.NewFact(uniFact)
	if err != nil {
		return err
	}

	forallXInSetDefinedByReplacement_ItIsInB := ast.NewUniFact([]string{"x"}, []ast.Fc{setAtom}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{ast.FcAtom("x"), setDefinedByReplacement.Params[1]})})
	err = e.NewFact(forallXInSetDefinedByReplacement_ItIsInB)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) inFactPostProcess_InFnTemplate(fact *ast.SpecFactStmt) (bool, error) {
	if _, ok := fact.Params[1].(*ast.FcFn); !ok {
		return false, nil
	}

	head, ok := fact.Params[1].(*ast.FcFn).IsFcFn_HasAtomHead_ReturnHead()
	if !ok {
		return false, nil
	}

	def, ok := e.GetFnTemplateDef_KeyIsFcHead(fact.Params[1].(*ast.FcFn))
	if !ok {
		return false, nil
	}

	fnTNoName, ok, err := e.getInstantiatedFnTTOfFcFn(fact.Params[1].(*ast.FcFn))
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	templateParamUniMap := map[string]ast.Fc{}
	for i, param := range def.TemplateDefHeader.Params {
		templateParamUniMap[param] = fact.Params[1].(*ast.FcFn).Params[i]
	}

	derivedFact, err := fnTNoName.DeriveUniFact(string(head), fact.Params[0], templateParamUniMap)
	if err != nil {
		return false, err
	}

	err = e.NewFact(derivedFact)
	if err != nil {
		return false, err
	}

	err = e.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fact.Params[0], fact.Params[1].(*ast.FcFn), fnTNoName)
	if err != nil {
		return false, err
	}

	return true, nil
}
