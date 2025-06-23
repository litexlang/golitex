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
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) checkSpecFactRequirements(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// 1. Check if all atoms in the parameters are declared
	for _, param := range stmt.Params {
		ok := ver.env.AreAtomsInFcAreDeclared(param, map[string]struct{}{})
		if !ok {
			return false, fmt.Errorf(env.AtomsInFcNotDeclaredMsg(param))
		}
	}

	// TODO: 这里有点问题。应该做的分类是：builtin的 stmt name，如in；以及非builtin的stmt name

	// 2. Check if the parameters satisfy the requirement of the function requirements
	for _, param := range stmt.Params {
		ok, err := ver.fcSatisfyFnRequirement(param, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, fmt.Errorf("parameters in %s do not satisfy the requirement of that function", param.String())
		}
	}

	// 所有的传入的参数符号 prop 的要求 以及 stmt name 确实是个 prop。这貌似不需要检查，因为每次你得到新的事实时候，已经检查过了
	// 但是最好在这里警告一下用户，如果不满足prop的要求的话，可能出问题

	return true, nil
}

func (ver *Verifier) fcSatisfyFnRequirement(fc ast.Fc, state VerState) (bool, error) {
	// 单独处理特殊的内置prop
	if isArithmeticFn(fc) {
		return ver.arithmeticFnRequirement(fc.(*ast.FcFn), state)
	} else {
		return ver.fcSatisfyNotBuiltinFnRequirement(fc, state)
	}
}

func isArithmeticFn(fc ast.Fc) bool {
	if ok := ast.IsFn_WithHeadNameInSlice(fc, []string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower, glob.KeySymbolPercent}); !ok {
		return false
	}

	return true
}

// TODO: 这里需要检查，setParam是否是自由变量
func (ver *Verifier) fcSatisfyNotBuiltinFnRequirement(fc ast.Fc, state VerState) (bool, error) {
	if fc.IsAtom() {
		return true, nil
	}

	asFcFn, ok := fc.(*ast.FcFn)
	if !ok {
		return false, fmt.Errorf("fc is not a function")
	}

	// TODO: Here we assume the fcFnHead is an atom. In the future we should support fcFnHead as a fcFn.
	fcFnHeadAsAtom, ok := asFcFn.FnHead.(*ast.FcAtom)
	if ok {
		fnDef, ok := ver.env.IsFnDeclared(fcFnHeadAsAtom)
		if !ok {
			return false, fmt.Errorf("%s is not a declared function", fcFnHeadAsAtom.String())
		}

		if fnDef != nil {
			ok, err := ver.fcFnParamsSatisfyFnHeadAtomRequirement(asFcFn, fnDef, state)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, fmt.Errorf("parameters in %s do not satisfy the requirement of that function", fcFnHeadAsAtom.String())
			}
		} else {
			return false, fmt.Errorf("builtin function %s is not implemented", fcFnHeadAsAtom.String())
		}
	} else {
		fcFnHeadAsFcFn, ok := asFcFn.FnHead.(*ast.FcFn)
		if !ok {
			return false, fmt.Errorf("fc is not a function")
		}

		templateOfFn, ok := ver.env.GetTemplateOfFn(fcFnHeadAsFcFn)
		if !ok {
			return false, fmt.Errorf("function %s is not implemented", fcFnHeadAsFcFn.String())
		}

		// 暂时还没有template，只有以fc形式出现的retSet
		ok, err := ver.fcFnParamsSatisfyFnTemplateRequirement(fcFnHeadAsFcFn, templateOfFn, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, fmt.Errorf("parameters in %s do not satisfy the requirement of that function", fcFnHeadAsFcFn.String())
		}
	}

	// 参数列表里的每个参数，内部的参数，符合参数列表里的参数的要求
	for _, param := range asFcFn.Params {
		ok, err := ver.fcSatisfyFnRequirement(param, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func (ver *Verifier) arithmeticFnRequirement(fc *ast.FcFn, state VerState) (bool, error) {
	// parameter必须是实数
	for _, param := range fc.Params {
		ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{param, ast.NewFcAtomWithName(glob.KeywordReal)}), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if ast.IsFcAtomWithNameAndEmptyPkg(fc.FnHead, glob.KeySymbolSlash) {
		// 分母不是0
		ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.FalsePure, ast.NewFcAtomWithName(glob.KeySymbolEqual), []ast.Fc{fc.Params[1], ast.NewFcAtomWithName("0")}), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
		return true, nil
	}

	if ast.IsFcAtomWithNameAndEmptyPkg(fc.FnHead, glob.KeySymbolPercent) {
		// 分母不是0
		ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.FalsePure, ast.NewFcAtomWithName(glob.KeySymbolEqual), []ast.Fc{fc.Params[1], ast.NewFcAtomWithName("0")}), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}

		// 分子分母必须是整数
		ok, err = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{fc.Params[0], ast.NewFcAtomWithName(glob.KeywordInt)}), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
		ok, err = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{fc.Params[1], ast.NewFcAtomWithName(glob.KeywordInt)}), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
		return true, nil
	}

	return true, nil
}

func (ver *Verifier) fcFnParamsSatisfyFnHeadAtomRequirement(asFcFn *ast.FcFn, fnDef *ast.DefFnStmt, state VerState) (bool, error) {
	fcFnHeadAsAtom, ok := asFcFn.FnHead.(*ast.FcAtom)
	if !ok {
		return false, fmt.Errorf(glob.NotImplementedMsg("function name is supposed to be an atom"))
	}

	if len(fnDef.DefHeader.SetParams) != len(asFcFn.Params) {
		return false, fmt.Errorf("function %s has %d params, but %d in sets", fcFnHeadAsAtom.String(), len(asFcFn.Params), len(fnDef.DefHeader.SetParams))
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range asFcFn.Params {
		uniMap[fnDef.DefHeader.Params[i]] = param
	}

	inFacts := []ast.FactStmt{}
	for i, inSet := range fnDef.DefHeader.SetParams {
		// 需要把setParam实例化，因为setParam可能包含自由变量
		setParam, err := inSet.Instantiate(uniMap)
		if err != nil {
			return false, err
		}
		inFact := ast.NewInFactWithFc(asFcFn.Params[i], setParam)
		inFacts = append(inFacts, inFact)
	}

	for _, inFact := range inFacts {
		ok, err := ver.VerFactStmt(inFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, fmt.Errorf("in fact %s is unknown", inFact.String())
		}
	}

	domFacts := []ast.FactStmt{}
	for _, domFact := range fnDef.DomFacts {
		fixed, err := domFact.Instantiate(uniMap)
		if err != nil {
			return false, err
		}
		domFacts = append(domFacts, fixed)
	}

	for _, domFact := range domFacts {
		ok, err := ver.VerFactStmt(domFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, fmt.Errorf("dom fact %s is unknown", domFact.String())
		}
	}

	return true, nil
}

func (ver *Verifier) fcFnParamsSatisfyFnTemplateRequirement(head *ast.FcFn, templateOfFn *ast.DefFnStmt, state VerState) (bool, error) {
	uniMap := map[string]ast.Fc{}
	for i, param := range head.Params {
		uniMap[templateOfFn.DefHeader.Params[i]] = param
	}

	paramSets, instantiatedDomFacts, _, _, err := templateOfFn.Instantiate_SetParamsInFacts_DomFacts_ThenFacts_RetSet(uniMap)
	if err != nil {
		return false, err
	}

	for i, paramSet := range paramSets {
		ok, err := ver.VerFactStmt(ast.NewInFactWithFc(head.Params[i], paramSet), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, fmt.Errorf("in fact %s is unknown", ast.NewInFactWithFc(head.Params[i], paramSet).String())
		}
	}

	for _, domFact := range instantiatedDomFacts {
		ok, err := ver.VerFactStmt(domFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, fmt.Errorf("dom fact %s is unknown", domFact.String())
		}
	}

	return true, nil
}
