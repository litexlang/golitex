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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	glob "golitex/glob"
)

// Verify a spec fact that is not a true equal fact
func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if ok, err := ver.checkSpecFactRequirements(stmt); err != nil {
		return false, err
	} else if !ok {
		return false, nil
	}

	if ok, err := ver.isSpecFactCommutative(stmt); err != nil {
		return false, err
	} else if !ok {
		return ver.verSpecFactStepByStep(stmt, state)
	} else {
		if ok, err := ver.verSpecFactStepByStep(stmt, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		} else {
			paramReversedStmt, err := stmt.ReverseSpecFactParamsOrder()
			if err != nil {
				return false, err
			}
			ok, err := ver.verSpecFactStepByStep(paramReversedStmt, state)
			if err == nil && ok {
				ver.successWithMsg(stmt.String(), "the proposition is commutative")
			}
			return ok, err
		}
	}
}

func (ver *Verifier) checkSpecFactRequirements(stmt *ast.SpecFactStmt) (bool, error) {
	// stmt参数里所有的涉及到的atom都已经被声明了
	for _, param := range stmt.Params {
		atoms := ast.GetAtomsInFc(param)
		for _, atom := range atoms {
			if !ver.env.IsAtomDeclared(atom) {
				return false, fmt.Errorf("%s is not declared", atom.String())
			}
		}
	}

	// if stmt.NameIs(glob.KeySymbolEqual) {
	// 	return true, nil
	// }

	if stmt.NameIs(glob.KeywordIn) {
		return ver.verSpecFactStepByStep(stmt, FinalRoundNoMsg)
	} else {
		// 所有函数内部的参数，都要符合函数的要求。这里必须要和in的情况分开，否则容易出问题，因为每次运行检查requirement的时候，都要检查一遍in的情况
		for _, param := range stmt.Params {
			ok, err := ver.fcSatisfyFnRequirement(param)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, fmt.Errorf("parameters in %s do not satisfy the requirement of that function", param.String())
			}
		}
	}

	// 所有的传入的参数符号 prop 的要求 以及 stmt name 确实是个 prop
	return true, nil
}

func (ver *Verifier) isSpecFactCommutative(stmt *ast.SpecFactStmt) (bool, error) {
	if stmt.NameIs(glob.KeySymbolEqual) {
		return true, nil
	}

	_ = stmt
	return false, nil
}

func (ver *Verifier) verSpecFactStepByStep(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if ok, err := ver.verSpecialSpecFact(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verSpecFactUseDefinition(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verSpecFact_SpecMem(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if !state.isFinalRound() {
		if ok, err := ver.verSpecFact_LogicMem(stmt, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}

		if ok, err := ver.verSpecFactUniMem(stmt, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verSpecialSpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.NameIs(glob.KeywordIn) {
		return ver.inFact(stmt, state)
	}

	if stmt.NameIs(glob.KeySymbolEqual) {
		return ver.verNotTrueEqualFact_BuiltinRules(stmt, state)
	}

	if stmt.NameIs(glob.KeywordProveByMathInduction) {
		return ver.mathInductionFact(stmt, state)
	}

	if stmt.NameIs(glob.KeywordCommutativeFn) {
		return ver.commutativeFnByDef(stmt, state)
	}

	if stmt.NameIs(glob.KeywordCommutativeProp) {
		return ver.btCommutativeRule(stmt, state)
	}

	if stmt.NameIs(glob.KeySymbolEqualEqual) {
		return ver.isFnEqualFact_Check(stmt, state)
	}

	if stmt.NameIs(glob.KeySymbolEqualEqualEqual) {
		return ver.isSetEqualFact_Check(stmt, state)
	}

	if ok, err := ver.btNumberLogicRelaOptBtRule(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) verSpecFactUseDefinition(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.IsPureFact() {
		return ver.specFactProveByDefinition(stmt, state)
	}

	if stmt.IsExist_St_Fact() {
		return ver.useExistPropDefProveExist_St(stmt, state)
	}

	return false, nil
}

func (ver *Verifier) specFactProveByDefinition(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	nextState := state.addRound()

	if !stmt.IsTrue() {
		return false, nil
	}

	defStmt, ok := ver.env.GetPropDef(stmt.PropName)
	if !ok {
		// 这里可能是因为这个propName是exist prop，所以没有定义
		return false, nil
	}

	if len(defStmt.IffFacts) == 0 {
		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
		return false, nil
	}

	iffToProp := defStmt.IffToPropUniFact()
	paramArrMap := map[string]ast.Fc{}
	for i, param := range stmt.Params {
		paramArrMap[defStmt.DefHeader.Params[i]] = param
	}

	// 本质上不需要把所有的参数都instantiate，只需要instantiate在dom里的就行
	instantiatedIffToProp, err := ast.InstantiateUniFact(iffToProp, paramArrMap)
	if err != nil {
		return false, err
	}
	// prove all domFacts are true
	for _, domFact := range instantiatedIffToProp.DomFacts {
		ok, err := ver.FactStmt(domFact, nextState)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), defStmt.String())
	} else {
		ver.successNoMsg()
	}

	return true, nil
}

func (ver *Verifier) useExistPropDefProveExist_St(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	sepIndex := stmt.Exist_St_SeparatorIndex()
	if sepIndex == -1 {
		return false, fmt.Errorf("%s has no separator", stmt.String())
	}

	propDef, ok := ver.env.GetExistPropDef(stmt.PropName)
	if !ok {
		// TODO: 如果没声明，应该报错
		return false, fmt.Errorf("%s has no definition", stmt.String())
	}

	uniConMap := map[string]ast.Fc{}
	for i := 0; i < sepIndex; i++ {
		uniConMap[propDef.ExistParams[i]] = stmt.Params[i]
	}

	for i := sepIndex + 1; i < len(stmt.Params); i++ {
		uniConMap[propDef.DefBody.DefHeader.Params[i-sepIndex-1]] = stmt.Params[i]
	}

	domFacts := []ast.FactStmt{}
	for _, fact := range propDef.DefBody.DomFacts {
		fixed, err := fact.Instantiate(uniConMap)
		if err != nil {
			return false, err
		}
		domFacts = append(domFacts, fixed)
	}

	thenFacts := []*ast.SpecFactStmt{}
	for _, thenFact := range propDef.DefBody.IffFacts {
		fixed, err := thenFact.Instantiate(uniConMap)
		if err != nil {
			return false, err
		}
		fixedAsSpecFact, ok := fixed.(*ast.SpecFactStmt)
		if !ok {
			return false, nil
			// 还是有可能then里不是 specFact的，比如定义可惜收敛；这时候我不报错，我只是让你不能证明 not exist。通常这种时候用法也都是 exist，用不着考虑not exist。你非要考虑not exist,那就用 not exist 来表示 forall，即给forall取个名字
			// return false, fmt.Errorf("instantiate spec fact stmt failed")
		}
		if !stmt.IsTrue() {
			fixedAsSpecFact = fixedAsSpecFact.ReverseTrue()
		}
		thenFacts = append(thenFacts, fixedAsSpecFact)
	}

	for _, domFact := range domFacts {
		ok, err := ver.FactStmt(domFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				msg := fmt.Sprintf("dom fact %s is unknown\n", domFact.String())
				ver.newMsgEnd(msg)
			}
			return false, nil
		}
	}

	for _, thenFact := range thenFacts {
		ok, err := ver.FactStmt(thenFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if state.requireMsg() {
		ver.successMsgEnd(stmt.String(), "")
	}

	return true, nil
}

func (ver *Verifier) verSpecFactSpecMemAndLogicMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.verSpecFact_SpecMem(stmt, state)
	if err != nil || ok {
		return ok, err
	}

	ok, err = ver.verSpecFact_LogicMem(stmt, state)
	if err != nil || ok {
		return ok, err
	}

	return false, nil
}

func (ver *Verifier) verSpecFactUniMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.verSpecFact_InSpecFact_UniMem(stmt, state)
	if err != nil || ok {
		return ok, err
	}

	return ver.verSpecFact_InLogicExpr_InUniFactMem(stmt, state)
}

func (ver *Verifier) verify_specFact_when_given_orStmt_is_true(stmt *ast.SpecFactStmt, orStmt *ast.OrStmt, index int, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchProp)
	defer ver.deleteEnvAndRetainMsg()

	// 其他是否都错
	for i := range orStmt.Facts {
		if i == index {
			continue
		}
		ok, err := ver.FactStmt(orStmt.Facts[i].ReverseTrue(), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), orStmt.String())
	} else {
		ver.successNoMsg()
	}

	return true, nil
}

func (ver *Verifier) fcSatisfyFnRequirement(fc ast.Fc) (bool, error) {
	if isArithmeticFn(fc) {
		return ver.arithmeticFnRequirement(fc.(*ast.FcFn))
	} else {
		return ver.fcSatisfyNotBuiltinFnRequirement(fc)
	}
	// return ver.fcSatisfyNotBuiltinFnRequirement(fc)
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

func isArithmeticFn(fc ast.Fc) bool {
	if ok, _ := ast.IsFn_WithHeadNameInSlice(fc, []string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower}); !ok {
		return false
	}

	return true
}

func (ver *Verifier) arithmeticFnRequirement(fc *ast.FcFn) (bool, error) {
	// parameter必须是实数
	for _, param := range fc.ParamSegs {
		ok, err := ver.FactStmt(ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{param, ast.NewFcAtomWithName(glob.KeywordReal)}), FinalRoundNoMsg)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if ast.IsFcAtomWithName(fc.FnHead, glob.KeySymbolSlash) {
		// 分母不是0
		ok, err := ver.FactStmt(ast.NewSpecFactStmt(ast.FalsePure, *ast.NewFcAtomWithName(glob.KeySymbolEqual), []ast.Fc{fc.ParamSegs[1], ast.NewFcAtomWithName("0")}), FinalRoundNoMsg)
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

func (ver *Verifier) verNotTrueEqualFact_BuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.IsTrue() {
		return false, nil
	}

	// 如果左右两边能是能被处理的数字
	areBothNumLit, areEqual, err := cmp.AreNumLit_Equal(stmt.Params[0], stmt.Params[1])
	if err != nil {
		return false, err
	}
	if areBothNumLit {
		if !areEqual {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), "builtin rules")
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
	}

	return false, nil
}
