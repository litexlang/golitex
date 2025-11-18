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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

func (e *Env) inFactPostProcess(fact *ast.SpecFactStmt) error {
	if len(fact.Params) != 2 {
		return fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact)
	}

	if def := e.GetSetFnRetValue(fact.Params[1]); def != nil {
		return e.inFactPostProcess_InSetFnRetValue(fact, def)
	}

	if isTemplate, err := e.inFactPostProcess_InFnTemplate(fact); isTemplate || err != nil {
		return err
	}

	if fnFn, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsFnTemplate_FcFn(fnFn) {
		// fnTNoName, err := fnFn.FnTFc_ToFnTNoName()
		// if err != nil {
		// 	return err
		// }

		fnTStruct, ok := ast.FcFnT_To_FnTStruct(fnFn)
		if !ok {
			return fmt.Errorf("%s is not fcFn type fn template", fnFn.String())
		}

		// err = e.InsertFnInFnTT(fact.Params[0], fnFn, fnTNoName)
		err := e.InsertFnInFnTT(fact.Params[0], fnTStruct)
		if err != nil {
			return err
		}

		return nil
	}

	if setDefinedByReplacement, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(setDefinedByReplacement.FnHead, glob.KeywordSetDefinedByReplacement) {
		return e.in_setDefinedByReplacement_postProcess(setDefinedByReplacement)
	}

	if cart, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cart.FnHead, glob.KeywordCart) {
		return e.in_cart_postProcess(fact)
	}

	return nil
}

func (e *Env) inFactPostProcess_InSetFnRetValue(fact *ast.SpecFactStmt, def *ast.HaveSetFnStmt) error {
	inFactRightParamAsFcFnPt, ok := fact.Params[1].(*ast.FnObj)
	if !ok {
		return fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact)
	}

	uniMap := map[string]ast.Obj{}
	for i, param := range def.DefHeader.Params {
		uniMap[param] = inFactRightParamAsFcFnPt.Params[i]
	}

	defToIntensionalSetStmt := def.ToIntensionalSetStmt()
	instantiated, err := defToIntensionalSetStmt.InstantiateFact(uniMap)
	if err != nil {
		return err
	}

	err = e.NewFact(instantiated)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) in_setDefinedByReplacement_postProcess(setDefinedByReplacement *ast.FnObj) error {
	uniFact := ast.ForallYInSetDefinedByReplacementThereIsXSTProp_X_YIsTrue(setDefinedByReplacement)
	err := e.NewFact(uniFact)
	if err != nil {
		return err
	}

	// forall x set_defined_by_replacement(A, B, P), x is in B
	forallXInSetDefinedByReplacement_ItIsInB := ast.NewUniFact([]string{"x"}, []ast.Obj{setDefinedByReplacement}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{ast.AtomObj("x"), setDefinedByReplacement.Params[1]}, glob.InnerGenLine)}, glob.InnerGenLine)
	err = e.NewFact(forallXInSetDefinedByReplacement_ItIsInB)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) SetEqualToSetDefinedByReplacement_PostProcess(setAtom ast.AtomObj, setDefinedByReplacement *ast.FnObj) error {
	uniFact := ast.ForallYInSetDefinedByReplacementThereIsXSTProp_X_YIsTrue(setDefinedByReplacement)
	uniFact.ParamSets[0] = setAtom
	err := e.NewFact(uniFact)
	if err != nil {
		return err
	}

	forallXInSetDefinedByReplacement_ItIsInB := ast.NewUniFact([]string{"x"}, []ast.Obj{setAtom}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{ast.AtomObj("x"), setDefinedByReplacement.Params[1]}, glob.InnerGenLine)}, glob.InnerGenLine)
	err = e.NewFact(forallXInSetDefinedByReplacement_ItIsInB)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) inFactPostProcess_InFnTemplate(fact *ast.SpecFactStmt) (bool, error) {
	if _, ok := fact.Params[1].(*ast.FnObj); !ok {
		return false, nil
	}

	head, ok := fact.Params[1].(*ast.FnObj).IsFcFn_HasAtomHead_ReturnHead()
	if !ok {
		return false, nil
	}

	def := e.GetFnTemplateDef_KeyIsFcHead(fact.Params[1].(*ast.FnObj))
	if def == nil {
		return false, nil
	}

	fnTNoName, ok, err := e.getInstantiatedFnTTOfFcFn(fact.Params[1].(*ast.FnObj))
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	templateParamUniMap := map[string]ast.Obj{}
	for i, param := range def.TemplateDefHeader.Params {
		templateParamUniMap[param] = fact.Params[1].(*ast.FnObj).Params[i]
	}

	derivedFact, err := fnTNoName.DeriveUniFact(string(head), fact.Params[0], templateParamUniMap)
	if err != nil {
		return false, err
	}

	err = e.NewFact(derivedFact)
	if err != nil {
		return false, err
	}

	err = e.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fact.Params[0], fact.Params[1].(*ast.FnObj), fnTNoName)
	if err != nil {
		return false, err
	}

	return true, nil
}

// 传入 x $in cart(x1, x2, ..., xn)
func (e *Env) in_cart_postProcess(fact *ast.SpecFactStmt) error {
	cart, ok := fact.Params[1].(*ast.FnObj)
	if !ok {
		return fmt.Errorf("expected cart to be FnObj, got %T", fact.Params[1])
	}

	// x $in set
	inSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{fact.Params[0], ast.AtomObj(glob.KeywordSet)}, glob.InnerGenLine)
	err := e.NewFact(inSetFact)
	if err != nil {
		return err
	}

	// 让 $is_cart(x) 成立
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIsCart), []ast.Obj{fact.Params[0]}, glob.InnerGenLine)
	err = e.NewFact(isCartFact)
	if err != nil {
		return err
	}

	// dim(x) = len(cart.Params)
	dimFn := ast.NewFnObj(ast.AtomObj(glob.KeywordDim), []ast.Obj{fact.Params[0]})
	dimValue := ast.AtomObj(strconv.Itoa(len(cart.Params)))
	dimEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeySymbolEqual), []ast.Obj{dimFn, dimValue}, glob.InnerGenLine)
	err = e.NewFact(dimEqualFact)
	if err != nil {
		return err
	}

	// proj(x, i+1) = cart.Params[i] for each i
	for i, cartParam := range cart.Params {
		projFn := ast.NewFnObj(ast.AtomObj(glob.KeywordProj), []ast.Obj{fact.Params[0], ast.AtomObj(strconv.Itoa(i + 1))})
		projEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeySymbolEqual), []ast.Obj{projFn, cartParam}, glob.InnerGenLine)
		err = e.NewFact(projEqualFact)
		if err != nil {
			return err
		}
	}

	return nil
}
