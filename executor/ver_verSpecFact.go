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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_UseCommutativity(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.TruePure {
		return ver.verTrueEqualFact(stmt, state, true)
	}

	if verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	// if ver.env.IsCommutativeProp(stmt) || (stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.FalsePure) {
	if ver.env.IsCommutativeProp(stmt) {
		reverseParamsOrderStmt, err := stmt.ReverseParameterOrder()
		if err != nil {
			return BoolErrToVerRet(false, err)
		}
		if verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(reverseParamsOrderStmt, state); verRet.IsTrue() || verRet.IsErr() {
			return verRet
		}
	}

	return BoolErrToVerRet(false, nil)
}

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_UseTransitivity(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	verRet := ver.verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(stmt, state)
	if verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	if stmt.TypeEnum == ast.TruePure && ver.env.IsTransitiveProp(string(stmt.PropName)) {
		relatedFcSlice := ver.env.GetRelatedFcSliceOfTransitiveProp(string(stmt.PropName), stmt.Params[0])
		if len(relatedFcSlice) == 0 {
			return BoolErrToVerRet(false, nil)
		}

		for _, relatedFc := range relatedFcSlice {
			relatedFcStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.PropName), []ast.Fc{relatedFc, stmt.Params[1]}, stmt.Line)
			verRet := ver.verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(relatedFcStmt, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				if state.WithMsg {
					ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is true by %s is a transitive prop and %s is true", stmt.String(), string(stmt.PropName), relatedFcStmt.String()))
				}
				return NewVerTrue(fmt.Sprintf("%s is true by %s is a transitive prop and %s is true", stmt.String(), string(stmt.PropName), relatedFcStmt.String()))
			}
		}
	}

	return BoolErrToVerRet(false, nil)
}

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	// replace the params with the values
	replaced, newStmt := ver.env.ReplaceFcInSpecFactWithValue(stmt)
	if replaced {
		verRet := ver.verSpecFactThatIsNotTrueEqualFactMainLogic(newStmt, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
			}
			return NewVerTrue(fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
		}
	}

	verRet := ver.verSpecFactThatIsNotTrueEqualFactMainLogic(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return NewVerTrue("")
	}

	return NewVerUnknown("")
}

// TODO: 其实 specFact 是等号的时候，还是会访问到这个函数。
// WARNING: 其实 specFact 是等号的时候，还是会访问到这个函数。所以这个函数的命名是有问题的
// WARNING: 需要重构整个架构，把验证的逻辑屡屡顺。Litex是ATP的话，那就必须要告诉用户我Auto的过程是什么样的
func (ver *Verifier) verSpecFactThatIsNotTrueEqualFactMainLogic(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	var verRet VerRet

	if !state.ReqOk {
		if verRet, state = ver.checkSpecFactReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}
	return ver.verSpecFactStepByStep(stmt, state)
}

func (ver *Verifier) verSpecFactStepByStep(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if verRet := ver.verSpecialSpecFact_ByBIR(stmt, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verSpecFact_BySpecMem(stmt, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verSpecFact_ByDEF(stmt, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if !state.isFinalRound() {
		if verRet := ver.verSpecFact_ByLogicMem(stmt, state); verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		if verRet := ver.verSpecFact_UniMem(stmt, state); verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verSpecialSpecFact_ByBIR(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if stmt.NameIs(glob.KeywordIn) {
		return ver.inFactBuiltinRules(stmt, state)
	} else if stmt.NameIs(glob.KeywordItemExistsIn) && stmt.TypeEnum == ast.TrueExist_St {
		return ver.trueExistInSt(stmt, state)
	}

	if verRet := ver.verNumberLogicRelaOpt_BuiltinRules(stmt, state); verRet.IsErr() {
		return verRet
	} else if verRet.IsTrue() {
		return verRet
	}

	if stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.FalsePure {
		return ver.verNotTrueEqualFact_BuiltinRules(stmt, state)
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verSpecFact_ByDEF(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if stmt.IsPureFact() {
		if !stmt.IsTrue() {
			return ver.verNotPureSpecFact_ByDef(stmt, state)
		}

		return ver.verPureSpecFact_ByDefinition(stmt, state)
	}

	if stmt.IsExist_St_Fact() {
		return ver.verExistSpecFact_ByDefinition(stmt, state)
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verPureSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	nextState := state.GetAddRound()

	curDefStmt := ver.env.GetPropDef(stmt.PropName)
	// defStmt := curDefStmt
	if curDefStmt == nil {
		// 这里可能是因为这个propName是exist prop，所以没有定义
		return NewVerUnknown("")
	}

	if len(curDefStmt.IffFacts) == 0 {
		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
		return NewVerUnknown("")
	}

	defStmt := ver.env.MakeUniFactParamsInThisDefPropDoNotConflictWithEnv(curDefStmt)

	iffToProp := defStmt.IffToPropUniFact()
	paramArrMap := map[string]ast.Fc{}
	for i, param := range stmt.Params {
		paramArrMap[defStmt.DefHeader.Params[i]] = param
	}

	// TODO: ? 这里还需要检查吗？或者说是在这里检查吗？难道prop的关于参数的检查不应该在更顶层的函数里？
	paramSetFacts, err := defStmt.DefHeader.GetInstantiatedParamInParamSetFact(paramArrMap)
	if err != nil {
		return BoolErrToVerRet(false, err)
	}

	for _, paramSetFact := range paramSetFacts {
		verRet := ver.VerFactStmt(paramSetFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	// 本质上不需要把所有的参数都instantiate，只需要instantiate在dom里的就行
	instantiatedIffToProp, err := ast.InstantiateUniFact(iffToProp, paramArrMap)
	if err != nil {
		return BoolErrToVerRet(false, err)
	}
	// prove all domFacts are true
	for _, domFact := range instantiatedIffToProp.DomFacts {
		verRet := ver.VerFactStmt(domFact, nextState)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), defStmt.String())
	}

	return NewVerTrue("")
}

func (ver *Verifier) verExistSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(stmt)

	propDef := ver.env.GetExistPropDef(stmt.PropName)
	if propDef == nil {
		// TODO: 如果没声明，应该报错
		return BoolErrToVerRet(false, fmt.Errorf("%s has no definition", stmt))
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
		return BoolErrToVerRet(false, err)
	}
	for i := range instParamSets {
		verRet := ver.VerFactStmt(ast.NewInFactWithFc(existParams[i], instParamSets[i]), state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			if state.WithMsg {
				msg := fmt.Sprintf("given object %s is not in its param set %s\n", existParams[i], instParamSets[i])
				ver.env.Msgs = append(ver.env.Msgs, msg)
			}
			return NewVerUnknown("")
		}
	}

	domFacts, err := propDef.DefBody.DomFacts.InstantiateFact(uniConMap)
	if err != nil {
		return BoolErrToVerRet(false, err)
	}

	iffFacts, err := propDef.DefBody.IffFacts.InstantiateFact(uniConMap)
	if err != nil {
		return BoolErrToVerRet(false, err)
	}

	for _, domFact := range domFacts {
		verRet := ver.VerFactStmt(domFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			if state.WithMsg {
				msg := fmt.Sprintf("dom fact %s is unknown\n", domFact)
				ver.env.Msgs = append(ver.env.Msgs, msg)
			}
			return NewVerUnknown("")
		}
	}

	for _, iffFact := range iffFacts {
		verRet := ver.VerFactStmt(iffFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), "by definition")
	}

	return NewVerTrue("")
}

// func (ver *Verifier) verSpecFactLogicMem(stmt *ast.SpecFactStmt, state *VerState) VerRet {
// 	verRet := ver.verSpecFact_ByLogicMem(stmt, state)
// 	if verRet.IsErr() || verRet.IsTrue() {
// 		return verRet.ToBoolErr()
// 	}
// 	return false, nil
// }

func (ver *Verifier) verSpecFact_UniMem(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	nextState := state.GetAddRound()

	verRet := ver.verSpecFact_InSpecFact_UniMem(stmt, nextState)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return ver.verSpecFact_InLogicExpr_InUniFactMem(stmt, nextState)
}

func (ver *Verifier) verNotTrueEqualFact_BuiltinRules(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if stmt.IsTrue() {
		return NewVerUnknown("")
	}

	// 如果左右两边能是能被处理的数字
	areBothNumLit, areEqual, err := cmp.NumLitEqual_ByEval(stmt.Params[0], stmt.Params[1])
	if err != nil {
		return NewVerErr(err.Error())
	}
	if areBothNumLit {
		if !areEqual { // 这里是在证明两边不相等
			ver.processOkMsg(state, stmt.String(), "builtin rules")
			return NewVerTrue("")
		}
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verNotPureSpecFact_ByDef(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	nextState := state.GetAddRound()

	defStmt := ver.env.GetPropDef(stmt.PropName)
	if defStmt == nil {
		// 这里可能是因为这个propName是exist prop，所以没有定义
		return NewVerUnknown("")
	}

	if len(defStmt.IffFacts) == 0 {
		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
		return NewVerUnknown("")
	}

	iffToProp := defStmt.IffToPropUniFact()
	paramArrMap := map[string]ast.Fc{}
	for i, param := range stmt.Params {
		paramArrMap[defStmt.DefHeader.Params[i]] = param
	}

	// TODO: ? 这里还需要检查吗？或者说是在这里检查吗？难道prop的关于参数的检查不应该在更顶层的函数里？
	paramSetFacts, err := defStmt.DefHeader.GetInstantiatedParamInParamSetFact(paramArrMap)
	if err != nil {
		return NewVerErr(err.Error())
	}

	for _, paramSetFact := range paramSetFacts {
		verRet := ver.VerFactStmt(paramSetFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	// 本质上不需要把所有的参数都instantiate，只需要instantiate在dom里的就行
	instantiatedIffToProp, err := ast.InstantiateUniFact(iffToProp, paramArrMap)
	if err != nil {
		return NewVerErr(err.Error())
	}

	// 某个fact是false的，那就OK了
	for _, domFact := range instantiatedIffToProp.DomFacts {
		domFactAsSpecFact, ok := domFact.(*ast.SpecFactStmt)
		if !ok {
			continue
		}
		reversedDomFact := domFactAsSpecFact.ReverseTrue()

		verRet := ver.VerFactStmt(reversedDomFact, nextState)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), defStmt.String())
			}

			return NewVerTrue("")
		}
	}

	return NewVerUnknown("")
}
