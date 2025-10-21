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

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	glob "golitex/glob"
	num "golitex/number"
)

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	ok, err := ver.verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if stmt.TypeEnum == ast.TruePure && ver.env.IsTransitiveProp(string(stmt.PropName)) {
		relatedFcSlice, ok := ver.env.GetRelatedFcSliceOfTransitiveProp(string(stmt.PropName), stmt.Params[0])
		if !ok {
			return false, nil
		}

		for _, relatedFc := range relatedFcSlice {
			relatedFcStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.PropName), []ast.Fc{relatedFc, stmt.Params[1]}, stmt.Line)
			ok, err := ver.verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(relatedFcStmt, state)
			if err != nil {
				return false, err
			}
			if ok {
				if state.WithMsg {
					ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is true by %s is a transitive prop and %s is true", stmt.String(), string(stmt.PropName), relatedFcStmt.String()))
				}
				return true, nil
			}
		}
	}

	return false, nil
}

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	// replace the params with the values
	replaced, newStmt := ver.env.ReplaceFcInSpecFact(stmt)
	if replaced {
		ok, err := ver.verSpecFactThatIsNotTrueEqualFactMainLogic(newStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
			}
			return true, nil
		}
	}

	ok, err := ver.verSpecFactThatIsNotTrueEqualFactMainLogic(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

// TODO: 其实 specFact 是等号的时候，还是会访问到这个函数。
// WARNING: 其实 specFact 是等号的时候，还是会访问到这个函数。所以这个函数的命名是有问题的
// WARNING: 需要重构整个架构，把验证的逻辑屡屡顺。Litex是ATP的话，那就必须要告诉用户我Auto的过程是什么样的
func (ver *Verifier) verSpecFactThatIsNotTrueEqualFactMainLogic(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	var ok bool
	var err error

	if !state.ReqOk {
		if ok, state, err = ver.checkSpecFactReq(stmt, state); err != nil || !ok {
			return false, err
		}
	}

	// ok, err = ver.isSpecFactCommutative(stmt)
	// if err != nil {
	// 	return false, err
	// }

	ok = stmt.IsPropNameEqual()

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

func (ver *Verifier) verSpecFactStepByStepNotCommutatively(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if (stmt.NameIs(glob.KeySymbolLargerEqual) || stmt.NameIs(glob.KeySymbolLessEqual) || stmt.NameIs(glob.KeySymbolGreater) || stmt.NameIs(glob.KeySymbolLess)) && stmt.IsTrue() {
		// TODO: 本质上这个逻辑应该放在BIR里
		return ver.verBtCmpSpecFact(stmt, state)
	}

	return ver.verSpecFactStepByStep(stmt, state)
}

// func (ver *Verifier) isSpecFactCommutative(stmt *ast.SpecFactStmt) (bool, error) {
// 	if stmt.NameIs(glob.KeySymbolEqual) {
// 		return true, nil
// 	}

// 	ok, err := ver.verSpecFact_BySpecMem(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordProveIsCommutativeProp), []ast.Fc{stmt.PropName}, stmt.Line), Round0NoMsg)
// 	if err != nil {
// 		return false, err
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	return false, nil
// }

func (ver *Verifier) verSpecFactStepByStep(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
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

func (ver *Verifier) verSpecialSpecFact_ByBIR(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if stmt.NameIs(glob.KeywordIn) {
		return ver.inFactBuiltinRules(stmt, state)
	} else if stmt.NameIs(glob.KeywordItemExistsIn) && stmt.TypeEnum == ast.TrueExist_St {
		return ver.trueExistInSt(stmt, state)
	}

	if ok, err := ver.verNumberLogicRelaOpt_BuiltinRules(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.FalsePure {
		return ver.verNotTrueEqualFact_BuiltinRules(stmt, state)
	}

	// if stmt.NameIs(glob.KeywordProveIsCommutativeProp) {
	// 	return ver.varCommutativeProp_BuiltinRules(stmt, state)
	// }

	return false, nil
}

func (ver *Verifier) verSpecFact_ByDEF(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if stmt.IsPureFact() {
		if !stmt.IsTrue() {
			return ver.verNotPureSpecFact_ByDef(stmt, state)
		}

		return ver.verPureSpecFact_ByDefinition(stmt, state)
	}

	if stmt.IsExist_St_Fact() {
		return ver.verExistSpecFact_ByDefinition(stmt, state)
	}

	return false, nil
}

func (ver *Verifier) verPureSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	nextState := state.GetAddRound()

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

	// TODO: ? 这里还需要检查吗？或者说是在这里检查吗？难道prop的关于参数的检查不应该在更顶层的函数里？
	paramSetFacts, err := defStmt.DefHeader.GetInstantiatedParamInParamSetFact(paramArrMap)
	if err != nil {
		return false, err
	}

	for _, paramSetFact := range paramSetFacts {
		ok, err := ver.VerFactStmt(paramSetFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
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

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), defStmt.String())
	}

	return true, nil
}

func (ver *Verifier) verExistSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(stmt)

	propDef, ok := ver.env.GetExistPropDef(stmt.PropName)
	if !ok {
		// TODO: 如果没声明，应该报错
		return false, fmt.Errorf("%s has no definition", stmt)
	}

	uniConMap := map[string]ast.Fc{}
	for i := range existParams {
		uniConMap[propDef.ExistParams[i]] = existParams[i]
	}

	for i := range factParams {
		uniConMap[propDef.DefBody.DefHeader.Params[i]] = factParams[i]
	}

	// given objects are in their param sets
	instParamSets, err := propDef.ExistParamSets.Instantiate(uniConMap)
	if err != nil {
		return false, err
	}
	for i := range instParamSets {
		ok, err := ver.VerFactStmt(ast.NewInFactWithFc(existParams[i], instParamSets[i]), state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.WithMsg {
				msg := fmt.Sprintf("given object %s is not in its param set %s\n", existParams[i], instParamSets[i])
				ver.env.Msgs = append(ver.env.Msgs, msg)
			}
			return false, nil
		}
	}

	domFacts, err := propDef.DefBody.DomFacts.Instantiate(uniConMap)
	if err != nil {
		return false, err
	}

	iffFacts, err := propDef.DefBody.IffFacts.Instantiate(uniConMap)
	if err != nil {
		return false, err
	}

	for _, domFact := range domFacts {
		ok, err := ver.VerFactStmt(domFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.WithMsg {
				msg := fmt.Sprintf("dom fact %s is unknown\n", domFact)
				ver.env.Msgs = append(ver.env.Msgs, msg)
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

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), "by definition")
	}

	return true, nil
}

func (ver *Verifier) verSpecFactLogicMem(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	var ok bool
	var err error

	ok, err = ver.verSpecFact_ByLogicMem(stmt, state)
	if isErrOrOk(ok, err) {
		return ok, err
	}

	return false, nil
}

func (ver *Verifier) verSpecFact_UniMem(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	nextState := state.GetAddRound()

	ok, err := ver.verSpecFact_InSpecFact_UniMem(stmt, nextState)
	if isErrOrOk(ok, err) {
		return ok, err
	}

	return ver.verSpecFact_InLogicExpr_InUniFactMem(stmt, nextState)
}

func (ver *Verifier) verNotTrueEqualFact_BuiltinRules(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if stmt.IsTrue() {
		return false, nil
	}

	// 如果左右两边能是能被处理的数字
	areBothNumLit, areEqual, err := cmp.NumLitEqual_ByEval(stmt.Params[0], stmt.Params[1])
	if err != nil {
		return false, err
	}
	if areBothNumLit {
		if !areEqual { // 这里是在证明两边不相等
			return ver.processOkMsg(state, stmt.String(), "builtin rules")
		}
	}

	return false, nil
}

var reverseCmpFcAtomMap = map[string]ast.FcAtom{
	glob.KeySymbolLargerEqual: ast.FcAtom(glob.KeySymbolLessEqual),
	glob.KeySymbolLessEqual:   ast.FcAtom(glob.KeySymbolLargerEqual),
	glob.KeySymbolGreater:     ast.FcAtom(glob.KeySymbolLess),
	glob.KeySymbolLess:        ast.FcAtom(glob.KeySymbolGreater),
}

// 只是证明 a >= b 和 b <= a 是等价的，没有用到 a = b => a >=b, a > b => a >= b，因为我觉得后者应该
// 其实也可以写入标准库而不是放在kernel，但我还是送给用户得了
// 传递性，就写在标准库吧
func (ver *Verifier) verBtCmpSpecFact(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	verBtCmp_ParamsAreLiteralNum, err := ver.verBtCmp_ParamsAreLiteralNum(stmt)
	if err != nil {
		return false, err
	}
	if verBtCmp_ParamsAreLiteralNum {
		if state.WithMsg {
			ver.successWithMsg(stmt.String(), "builtin rules")
		}
		return true, nil
	}

	propName := string(stmt.PropName)

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
		greaterStmt.PropName = ast.FcAtom(glob.KeySymbolGreater)
		ok, err = ver.verSpecFactStepByStep(&greaterStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.processOkMsg(state, stmt.String(), fmt.Sprintf("%s is true", greaterStmt.String()))
		}

		// 尝试证明 =
		equalStmt := *stmt
		equalStmt.PropName = ast.FcAtom(glob.KeySymbolEqual)
		ok, err = ver.verTrueEqualFact(&equalStmt, state, true)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.processOkMsg(state, stmt.String(), fmt.Sprintf("%s is true", equalStmt.String()))
		}
	}

	// 如果 <= 操作符，尝试证明 < 或 = 是否成立
	if propName == glob.KeySymbolLessEqual {
		// 尝试证明 <
		lessStmt := *stmt
		lessStmt.PropName = ast.FcAtom(glob.KeySymbolLess)
		ok, err = ver.verSpecFactStepByStep(&lessStmt, state)
		if isErrOrOk(ok, err) {
			return ok, err
		}

		// 尝试证明 =
		equalStmt := *stmt
		equalStmt.PropName = ast.FcAtom(glob.KeySymbolEqual)
		ok, err = ver.verTrueEqualFact(&equalStmt, state, true)
		if isErrOrOk(ok, err) {
			return ok, err
		}
	}

	if propName == glob.KeySymbolGreater || propName == glob.KeySymbolLess {
		reversedStmt, err := stmt.ReverseSpecFactParamsOrder()
		if err != nil {
			return false, err
		}
		reversedStmt.PropName = reversePropName
		ok, err = ver.verSpecFactStepByStep(reversedStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.processOkMsg(state, stmt.String(), fmt.Sprintf("%s is true", reversedStmt))
		}
		return false, nil
	}

	return false, nil
}

func (ver *Verifier) verBtCmp_ParamsAreLiteralNum(stmt *ast.SpecFactStmt) (bool, error) {
	// 用 glob 里的 NumLitExpr 去比较
	_, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[0])
	if err != nil || !ok {
		return false, nil
	}
	_, ok, err = ast.MakeFcIntoNumLitExpr(stmt.Params[1])
	if err != nil || !ok {
		return false, nil
	}

	left, err := num.CalculatorEval(stmt.Params[0].String())
	if err != nil {
		return false, nil
	}
	right, err := num.CalculatorEval(stmt.Params[1].String())
	if err != nil {
		return false, nil
	}

	switch stmt.PropName {
	case glob.KeySymbolLargerEqual:
		return left >= right, nil
	case glob.KeySymbolLessEqual:
		return left <= right, nil
	case glob.KeySymbolGreater:
		return left > right, nil
	case glob.KeySymbolLess:
		return left < right, nil
	}

	return false, nil
}

func (ver *Verifier) verNotPureSpecFact_ByDef(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	nextState := state.GetAddRound()

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

	// TODO: ? 这里还需要检查吗？或者说是在这里检查吗？难道prop的关于参数的检查不应该在更顶层的函数里？
	paramSetFacts, err := defStmt.DefHeader.GetInstantiatedParamInParamSetFact(paramArrMap)
	if err != nil {
		return false, err
	}

	for _, paramSetFact := range paramSetFacts {
		ok, err := ver.VerFactStmt(paramSetFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	// 本质上不需要把所有的参数都instantiate，只需要instantiate在dom里的就行
	instantiatedIffToProp, err := ast.InstantiateUniFact(iffToProp, paramArrMap)
	if err != nil {
		return false, err
	}

	// 某个fact是false的，那就OK了
	for _, domFact := range instantiatedIffToProp.DomFacts {
		domFactAsSpecFact, ok := domFact.(*ast.SpecFactStmt)
		if !ok {
			continue
		}
		reversedDomFact := domFactAsSpecFact.ReverseTrue()

		ok, err := ver.VerFactStmt(reversedDomFact, nextState)
		if err != nil {
			return false, err
		}
		if ok {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), defStmt.String())
			}

			return true, nil
		}
	}

	return false, nil
}
