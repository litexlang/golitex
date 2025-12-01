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

func (e *Env) inFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	if def := e.GetSetFnRetValue(fact.Params[1]); def != nil {
		return e.inFactPostProcess_InSetFnRetValue(fact, def)
	}

	isTemplate, ret := e.inFactPostProcess_InFnTemplate(fact)
	if ret.IsErr() {
		return ret
	}
	if isTemplate {
		return glob.TrueRet("")
	}

	if fnFn, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsFnTemplate_FcFn(fnFn) {
		// fnTNoName, err := fnFn.FnTFc_ToFnTNoName()
		// if err != nil {
		// 	return err
		// }

		fnTStruct, ok := ast.FcFnT_To_FnTStruct(fnFn)
		if !ok {
			return glob.ErrRet(fmt.Errorf("%s is not fcFn type fn template", fnFn.String()))
		}

		// err = e.InsertFnInFnTT(fact.Params[0], fnFn, fnTNoName)
		ret := e.InsertFnInFnTT(fact.Params[0], fnTStruct)
		if ret.IsErr() {
			return ret
		}

		return glob.TrueRet("")
	}

	return glob.TrueRet("")
}

func (e *Env) inFactPostProcess_InSetFnRetValue(fact *ast.SpecFactStmt, def *ast.HaveSetFnStmt) glob.GlobRet {
	inFactRightParamAsFcFnPt, ok := fact.Params[1].(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	uniMap := map[string]ast.Obj{}
	for i, param := range def.DefHeader.Params {
		uniMap[param] = inFactRightParamAsFcFnPt.Params[i]
	}

	defToIntensionalSetStmt := def.ToIntensionalSetStmt()
	instantiated, err := defToIntensionalSetStmt.InstantiateFact(uniMap)
	if err != nil {
		return glob.ErrRet(err)
	}

	ret := e.NewFact(instantiated)
	if ret.IsErr() {
		return ret
	}

	return glob.TrueRet("")
}

func (e *Env) inFactPostProcess_InFnTemplate(fact *ast.SpecFactStmt) (bool, glob.GlobRet) {
	if _, ok := fact.Params[1].(*ast.FnObj); !ok {
		return false, glob.TrueRet("")
	}

	head, ok := fact.Params[1].(*ast.FnObj).IsFcFn_HasAtomHead_ReturnHead()
	if !ok {
		return false, glob.TrueRet("")
	}

	def := e.GetFnTemplateDef_KeyIsFcHead(fact.Params[1].(*ast.FnObj))
	if def == nil {
		return false, glob.TrueRet("")
	}

	fnTNoName, ok, ret := e.getInstantiatedFnTTOfFcFn(fact.Params[1].(*ast.FnObj))
	if ret.IsErr() {
		return false, ret
	}
	if !ok {
		return false, glob.TrueRet("")
	}

	templateParamUniMap := map[string]ast.Obj{}
	for i, param := range def.TemplateDefHeader.Params {
		templateParamUniMap[param] = fact.Params[1].(*ast.FnObj).Params[i]
	}

	derivedFact, err := fnTNoName.DeriveUniFact(string(head), fact.Params[0], templateParamUniMap)
	if err != nil {
		return false, glob.ErrRet(err)
	}

	ret = e.NewFact(derivedFact)
	if ret.IsErr() {
		return false, ret
	}

	ret = e.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fact.Params[0], fact.Params[1].(*ast.FnObj), fnTNoName)
	if ret.IsErr() {
		return false, ret
	}

	return true, glob.TrueRet("")
}

// 传入 x = cart(x1, x2, ..., xn)
func (e *Env) equalFactPostProcess_cart(fact *ast.SpecFactStmt) glob.GlobRet {
	cart, ok := fact.Params[1].(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("expected cart to be FnObj, got %T", fact.Params[1]))
	}

	// x $in set
	inSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fact.Params[0], ast.Atom(glob.KeywordSet)}, glob.InnerGenLine)
	ret := e.NewFact(inSetFact)
	if ret.IsErr() {
		return ret
	}

	// 让 $is_cart(x) 成立
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fact.Params[0]}, glob.InnerGenLine)
	ret = e.NewFact(isCartFact)
	if ret.IsErr() {
		return ret
	}

	// dim(x) = len(cart.Params)
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{fact.Params[0]})
	dimValue := ast.Atom(strconv.Itoa(len(cart.Params)))
	dimEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{dimFn, dimValue}, glob.InnerGenLine)
	ret = e.NewFact(dimEqualFact)
	if ret.IsErr() {
		return ret
	}

	// proj(x, i+1) = cart.Params[i] for each i
	for i, cartParam := range cart.Params {
		projFn := ast.NewFnObj(ast.Atom(glob.KeywordProj), []ast.Obj{fact.Params[0], ast.Atom(strconv.Itoa(i + 1))})
		projEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{projFn, cartParam}, glob.InnerGenLine)
		ret = e.NewFact(projEqualFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.TrueRet("")
}
