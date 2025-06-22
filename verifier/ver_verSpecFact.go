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
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if ok, err := ver.checkSpecFactRequirements(stmt, state); err != nil {
		return false, err
	} else if !ok {
		return false, nil
	}

	ok, err := ver.isSpecFactCommutative(stmt)
	if err != nil {
		return false, err
	}

	if !ok {
		return ver.verSpecFactStepByStepNotCommutatively(stmt, state)
	} else {
		ok, err := ver.verSpecFactStepByStepNotCommutatively(stmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
		reversedStmt, err := stmt.ReverseSpecFactParamsOrder()
		if err != nil {
			return false, err
		}
		ok, err = ver.verSpecFactStepByStepNotCommutatively(reversedStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
		return false, nil
	}
}

func (ver *Verifier) verSpecFactStepByStepNotCommutatively(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.NameIs(glob.KeySymbolLargerEqual) || stmt.NameIs(glob.KeySymbolLessEqual) || stmt.NameIs(glob.KeySymbolGreater) || stmt.NameIs(glob.KeySymbolLess) {
		return ver.verBtCmpSpecFact(stmt, state)
	}

	return ver.verSpecFactStepByStep(stmt, state)
}

func (ver *Verifier) isSpecFactCommutative(stmt *ast.SpecFactStmt) (bool, error) {
	if stmt.NameIs(glob.KeySymbolEqual) {
		return true, nil
	}

	ok, err := ver.verSpecFact_BySpecMem(ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordCommutativeProp), []ast.Fc{&stmt.PropName}), Round0NoMsg)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) verSpecFactStepByStep(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if ok, err := ver.verSpecialSpecFact_ByBIR(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verSpecFact_BySpecMem(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verSpecFact_ByDEF(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if !state.isFinalRound() {
		if ok, err := ver.verSpecFact_ByLogicMem(stmt, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}

		if ok, err := ver.verSpecFact_UniMem(stmt, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verSpecialSpecFact_ByBIR(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.NameIs(glob.KeywordIn) {
		return ver.inFactBuiltinRules(stmt, state)
	}

	if ok, err := ver.verNumberLogicRelaOpt_BuiltinRules(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if stmt.NameIs(glob.KeySymbolEqual) {
		return ver.verNotTrueEqualFact_BuiltinRules(stmt, state)
	}

	if stmt.NameIs(glob.KeywordProveByMathInduction) {
		return ver.mathInductionFact_BuiltinRules(stmt, state)
	}

	if stmt.NameIs(glob.KeywordCommutativeProp) {
		return ver.varCommutativeProp_BuiltinRules(stmt, state)
	}

	if stmt.NameIs(glob.KeySymbolEqualEqual) {
		return ver.isFnEqualFact_Check_BuiltinRules(stmt, state)
	}

	if stmt.NameIs(glob.KeySymbolEqualEqualEqual) {
		return ver.isSetEqualFact_Check_BuiltinRules(stmt, state)
	}

	return false, nil
}

func (ver *Verifier) verSpecFact_ByDEF(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.IsPureFact() {
		return ver.verPureSpecFact_ByDefinition(stmt, state)
	}

	if stmt.IsExist_St_Fact() {
		return ver.verExistSpecFact_ByDefinition(stmt, state)
	}

	return false, nil
}

func (ver *Verifier) verPureSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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
		ok, err := ver.VerFactStmt(domFact, nextState)
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

func (ver *Verifier) verExistSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(stmt)

	propDef, ok := ver.env.GetExistPropDef(stmt.PropName)
	if !ok {
		// TODO: 如果没声明，应该报错
		return false, fmt.Errorf("%s has no definition", stmt.String())
	}

	uniConMap := map[string]ast.Fc{}
	for i := 0; i < len(existParams); i++ {
		uniConMap[propDef.ExistParams[i]] = existParams[i]
	}

	for i := 0; i < len(factParams); i++ {
		uniConMap[propDef.DefBody.DefHeader.Params[i]] = factParams[i]
	}

	domFacts := []ast.FactStmt{}
	for _, fact := range propDef.DefBody.DomFacts {
		fixed, err := fact.Instantiate(uniConMap)
		if err != nil {
			return false, err
		}
		domFacts = append(domFacts, fixed)
	}

	iffFacts := []ast.FactStmt{}
	for _, iffFact := range propDef.DefBody.IffFacts {
		fixed, err := iffFact.Instantiate(uniConMap)
		if err != nil {
			return false, err
		}
		iffFacts = append(iffFacts, fixed)
	}

	for _, domFact := range domFacts {
		ok, err := ver.VerFactStmt(domFact, state)
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

	for _, iffFact := range iffFacts {
		ok, err := ver.VerFactStmt(iffFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if state.requireMsg() {
		ver.successMsgEnd(stmt.String(), "by definition")
	}

	return true, nil
}

func (ver *Verifier) verSpecFact_SpecMemAndLogicMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.verSpecFact_BySpecMem(stmt, state)
	if err != nil || ok {
		return ok, err
	}

	ok, err = ver.verSpecFact_ByLogicMem(stmt, state)
	if err != nil || ok {
		return ok, err
	}

	return false, nil
}

func (ver *Verifier) verSpecFact_UniMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.verSpecFact_InSpecFact_UniMem(stmt, state)
	if err != nil || ok {
		return ok, err
	}

	return ver.verSpecFact_InLogicExpr_InUniFactMem(stmt, state)
}

func (ver *Verifier) verNotTrueEqualFact_BuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.IsTrue() {
		return false, nil
	}

	// 如果左右两边能是能被处理的数字
	areBothNumLit, areEqual, err := cmp.NumLitEqual_ByEval(stmt.Params[0], stmt.Params[1])
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

var reverseCmpFcAtomMap = map[string]*ast.FcAtom{
	glob.KeySymbolLargerEqual: ast.NewFcAtomWithName(glob.KeySymbolLessEqual),
	glob.KeySymbolLessEqual:   ast.NewFcAtomWithName(glob.KeySymbolLargerEqual),
	glob.KeySymbolGreater:     ast.NewFcAtomWithName(glob.KeySymbolLess),
	glob.KeySymbolLess:        ast.NewFcAtomWithName(glob.KeySymbolGreater),
}

// 只是证明 a >= b 和 b <= a 是等价的，没有用到 a = b => a >=b, a > b => a >= b，因为我觉得后者应该
// 其实也可以写入标准库而不是放在kernel，但我还是送给用户得了
// 传递性，就写在标准库吧
func (ver *Verifier) verBtCmpSpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	propName := stmt.PropName.Name

	reversePropName := reverseCmpFcAtomMap[propName]

	ok, err := ver.verSpecFactStepByStep(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// 如果是 >= 操作符，尝试证明 > 或 = 是否成立
	if propName == glob.KeySymbolLargerEqual {
		// 尝试证明 >
		greaterStmt := *stmt
		greaterStmt.PropName = *ast.NewFcAtomWithName(glob.KeySymbolGreater)
		ok, err = ver.verSpecFactStepByStep(&greaterStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is true", greaterStmt.String()))
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}

		// 尝试证明 =
		equalStmt := *stmt
		equalStmt.PropName = *ast.NewFcAtomWithName(glob.KeySymbolEqual)
		ok, err = ver.verTrueEqualFact(&equalStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is true", equalStmt.String()))
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
	}

	// 如果 <= 操作符，尝试证明 < 或 = 是否成立
	if propName == glob.KeySymbolLessEqual {
		// 尝试证明 <
		lessStmt := *stmt
		lessStmt.PropName = *ast.NewFcAtomWithName(glob.KeySymbolLess)
		ok, err = ver.verSpecFactStepByStep(&lessStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}

		// 尝试证明 =
		equalStmt := *stmt
		equalStmt.PropName = *ast.NewFcAtomWithName(glob.KeySymbolEqual)
		ok, err = ver.verTrueEqualFact(&equalStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	if propName == glob.KeySymbolGreater || propName == glob.KeySymbolLess {
		reversedStmt, err := stmt.ReverseSpecFactParamsOrder()
		if err != nil {
			return false, err
		}
		reversedStmt.PropName = *reversePropName
		ok, err = ver.verSpecFactStepByStep(reversedStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is true", reversedStmt.String()))
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
		return false, nil
	}

	return false, fmt.Errorf("unknown comparison operator: %s", propName)
}
