package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) checkSpecFactRequirements(stmt *ast.SpecFactStmt) (bool, error) {
	// 1. Check if all atoms in the parameters are declared
	for _, param := range stmt.Params {
		atoms := ast.GetAtomsInFc(param)
		for _, atom := range atoms {
			if !ver.env.IsAtomDeclared(atom) {
				return false, fmt.Errorf("%s is not declared", atom.String())
			}
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
			ok, err := ver.FactStmt(inFact, FinalRoundNoMsg)
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
			ok, err := ver.FactStmt(domFact, FinalRoundNoMsg)
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
