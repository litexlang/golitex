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
	glob "golitex/glob"
)

func (ver *Verifier) checkSpecFactRequirements(stmt *ast.SpecFactStmt) (bool, error) {
	// 1. Check if all atoms in the parameters are declared
	for _, param := range stmt.Params {
		ok := ver.env.AtomsInFcAreDeclared(param)
		if !ok {
			return false, fmt.Errorf("some atoms in %s are undeclared", param.String())
		}
	}

	// TODO: 这里有点问题。应该做的分类是：builtin的 stmt name，如in；以及非builtin的stmt name

	// 2. Check if the parameters satisfy the requirement of the function requirements
	for _, param := range stmt.Params {
		ok, err := ver.fcSatisfyFnRequirement(param)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, fmt.Errorf("parameters in %s do not satisfy the requirement of that function", param.String())
		}
	}

	// 所有的传入的参数符号 prop 的要求 以及 stmt name 确实是个 prop
	return true, nil
}

func (ver *Verifier) fcSatisfyFnRequirement(fc ast.Fc) (bool, error) {
	if isArithmeticFn(fc) {
		return ver.arithmeticFnRequirement(fc.(*ast.FcFn))
	} else {
		return ver.fcSatisfyNotBuiltinFnRequirement(fc)
	}
}

func isArithmeticFn(fc ast.Fc) bool {
	if ok := ast.IsFn_WithHeadNameInSlice(fc, []string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower}); !ok {
		return false
	}

	return true
}

// TODO: 这里需要检查，setParam是否是自由变量
func (ver *Verifier) fcSatisfyNotBuiltinFnRequirement(fc ast.Fc) (bool, error) {
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
		return false, fmt.Errorf("function %s is not declared", fcFnHeadAsAtom.String())
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
			ok, err := ver.VerFactStmt(inFact, FinalRoundNoMsg)
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
			ok, err := ver.VerFactStmt(domFact, FinalRoundNoMsg)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, fmt.Errorf("dom fact %s is unknown", domFact.String())
			}
		}
	}

	for _, param := range asFcFn.ParamSegs {
		ok, err := ver.fcSatisfyFnRequirement(param)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func (ver *Verifier) arithmeticFnRequirement(fc *ast.FcFn) (bool, error) {
	// parameter必须是实数
	for _, param := range fc.ParamSegs {
		ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{param, ast.NewFcAtomWithName(glob.KeywordReal)}), FinalRoundNoMsg)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if ast.IsFcAtomWithNameAndEmptyPkg(fc.FnHead, glob.KeySymbolSlash) {
		// 分母不是0
		ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.FalsePure, ast.NewFcAtomWithName(glob.KeySymbolEqual), []ast.Fc{fc.ParamSegs[1], ast.NewFcAtomWithName("0")}), FinalRoundNoMsg)
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
