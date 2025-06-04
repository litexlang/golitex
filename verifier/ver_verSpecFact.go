// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verSpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if ok, err := ver.isValidSpecFact(stmt); err != nil {
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

func (ver *Verifier) isValidSpecFact(stmt *ast.SpecFactStmt) (bool, error) {
	// stmt参数里所有的涉及到的atom都已经被声明了
	for _, param := range stmt.Params {
		atoms := ast.GetAtomsInFc(param)
		for _, atom := range atoms {
			if !ver.env.IsAtomDeclared(atom) {
				return false, fmt.Errorf("%s is not declared", atom.String())
			}
		}
	}

	// 所有函数内部的参数，都要符合函数的要求

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
	if stmt.NameIs(glob.KeywordProveByMathInduction) {
		return ver.mathInductionFact(stmt, state)
	}

	if stmt.NameIs(glob.KeywordCommutativeFn) {
		return ver.commutativeFnByDef(stmt, state)
	}

	if stmt.NameIs(glob.KeywordCommutativeProp) {
		return ver.btCommutativeRule(stmt, state)
	}

	if stmt.NameIs(glob.KeywordIn) {
		return ver.inFact(stmt, state)
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
	ver.newEnv(ver.env, ver.env.CurMatchEnv)
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

func (ver *Verifier) inFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("invalid number of parameters for in fact")
	}

	if ast.IsFcAtomWithName(stmt.Params[1], glob.KeywordObj) {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "everything is in the obj set")
		} else {
			ver.successNoMsg()
		}
		return true, nil
	}

	ok, err := ver.btLitNumInNatOrIntOrRatOrRealOrComplex(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}
