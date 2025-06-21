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
// Litex Zulip community: https://litex.zulipchat.com

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
	if isArithmeticFn(fc) {
		return ver.arithmeticFnRequirement(fc.(*ast.FcFn), state)
	} else {
		return ver.fcSatisfyNotBuiltinFnRequirement(fc, state)
	}
}

func isArithmeticFn(fc ast.Fc) bool {
	if ok := ast.IsFn_WithHeadNameInSlice(fc, []string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower}); !ok {
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
	if !ok {
		return false, fmt.Errorf(glob.NotImplementedMsg("function name is supposed to be an atom"))
	}

	fnDef, ok := ver.env.IsFnDeclared(fcFnHeadAsAtom)
	if !ok {
		return false, fmt.Errorf("%s is not a declared function", fcFnHeadAsAtom.String())
	}

	// fnDef == nil means the function is builtin
	if fnDef != nil {
		if len(fnDef.DefHeader.SetParams) != len(asFcFn.ParamSegs) {
			return false, fmt.Errorf("function %s has %d params, but %d in sets", fcFnHeadAsAtom.String(), len(asFcFn.ParamSegs), len(fnDef.DefHeader.SetParams))
		}

		uniMap := map[string]ast.Fc{}
		for i, param := range asFcFn.ParamSegs {
			uniMap[fnDef.DefHeader.Params[i]] = param
		}

		inFacts := []ast.FactStmt{}
		for i, inSet := range fnDef.DefHeader.SetParams {
			// 需要把setParam实例化，因为setParam可能包含自由变量
			setParam, err := inSet.Instantiate(uniMap)
			if err != nil {
				return false, err
			}
			inFact := ast.NewInFactWithFc(asFcFn.ParamSegs[i], setParam)
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
	}

	for _, param := range asFcFn.ParamSegs {
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
	for _, param := range fc.ParamSegs {
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
		ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.FalsePure, ast.NewFcAtomWithName(glob.KeySymbolEqual), []ast.Fc{fc.ParamSegs[1], ast.NewFcAtomWithName("0")}), state)
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
