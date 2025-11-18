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

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_UseCommutativity(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.TruePure {
		return ver.verTrueEqualFact(stmt, state, true)
	}

	if verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	// if ver.env.IsCommutativeProp(stmt) || (stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.FalsePure) {
	if ver.Env.IsCommutativeProp(stmt) {
		reverseParamsOrderStmt, err := stmt.ReverseParameterOrder()
		if err != nil {
			return BoolErrToExecRet(false, err)
		}
		if verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(reverseParamsOrderStmt, state); verRet.IsTrue() || verRet.IsErr() {
			return verRet
		}
	}

	if verRet := ver.UseBuiltinRulesForSpecialSpecFact(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return BoolErrToExecRet(false, nil)
}

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_UseTransitivity(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	verRet := ver.verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(stmt, state)
	if verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	if stmt.TypeEnum == ast.TruePure && ver.Env.IsTransitiveProp(string(stmt.PropName)) {
		relatedFcSlice := ver.Env.GetRelatedFcSliceOfTransitiveProp(string(stmt.PropName), stmt.Params[0])
		if len(relatedFcSlice) == 0 {
			return BoolErrToExecRet(false, nil)
		}

		for _, relatedFc := range relatedFcSlice {
			relatedFcStmt := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(stmt.PropName), []ast.Obj{relatedFc, stmt.Params[1]}, stmt.Line)
			verRet := ver.verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(relatedFcStmt, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				msg := fmt.Sprintf("%s is true by %s is a transitive prop and %s is true", stmt.String(), string(stmt.PropName), relatedFcStmt.String())
				return ver.maybeAddSuccessMsg(state, stmt.String(), msg, NewExecTrue(""))
			}
		}
	}

	return BoolErrToExecRet(false, nil)
}

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// replace the params with the values
	replaced, newStmt := ver.Env.ReplaceFcInSpecFactWithValue(stmt)
	if replaced {
		verRet := ver.verSpecFactThatIsNotTrueEqualFactMainLogic(newStmt, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			msg := fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String())
			return ver.maybeAddSuccessMsg(state, stmt.String(), msg, NewExecTrue(""))
		}
	}

	verRet := ver.verSpecFactThatIsNotTrueEqualFactMainLogic(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	return NewExecUnknown("")
}

// TODO: 其实 specFact 是等号的时候，还是会访问到这个函数。
// WARNING: 其实 specFact 是等号的时候，还是会访问到这个函数。所以这个函数的命名是有问题的
// WARNING: 需要重构整个架构，把验证的逻辑屡屡顺。Litex是ATP的话，那就必须要告诉用户我Auto的过程是什么样的
func (ver *Verifier) verSpecFactThatIsNotTrueEqualFactMainLogic(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	var verRet ExecRet

	if !state.ReqOk {
		if verRet, state = ver.checkSpecFactReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}
	return ver.verSpecFactStepByStep(stmt, state)
}

func (ver *Verifier) verSpecFactStepByStep(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
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

	return NewExecUnknown("")
}

func (ver *Verifier) verSpecialSpecFact_ByBIR(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
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
		return ver.verNotTrueEqualFact_BuiltinRules_WithState(stmt, state)
	}

	return NewExecUnknown("")
}

func (ver *Verifier) verSpecFact_ByDEF(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if stmt.IsPureFact() {
		if !stmt.IsTrue() {
			return ver.verNotPureSpecFact_ByDef(stmt, state)
		}

		return ver.verPureSpecFact_ByDefinition(stmt, state)
	}

	if stmt.IsExist_St_Fact() {
		return ver.verExistSpecFact_ByDefinition(stmt, state)
	}

	return NewExecUnknown("")
}

func (ver *Verifier) verPureSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	nextState := state.GetAddRound()

	curDefStmt := ver.Env.GetPropDef(stmt.PropName)
	// defStmt := curDefStmt
	if curDefStmt == nil {
		// 这里可能是因为这个propName是exist prop，所以没有定义
		return NewExecUnknown("")
	}

	if len(curDefStmt.IffFacts) == 0 {
		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
		return NewExecUnknown("")
	}

	defStmt := ver.Env.MakeUniFactParamsInThisDefPropDoNotConflictWithEnv(curDefStmt)

	iffToProp := defStmt.IffToPropUniFact()
	paramArrMap := map[string]ast.Obj{}
	for i, param := range stmt.Params {
		paramArrMap[defStmt.DefHeader.Params[i]] = param
	}

	// TODO: ? 这里还需要检查吗？或者说是在这里检查吗？难道prop的关于参数的检查不应该在更顶层的函数里？
	paramSetFacts, err := defStmt.DefHeader.GetInstantiatedParamInParamSetFact(paramArrMap)
	if err != nil {
		return BoolErrToExecRet(false, err)
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
		return BoolErrToExecRet(false, err)
	}
	// prove all domFacts are true
	for _, domFact := range instantiatedIffToProp.DomFacts {
		verRet := ver.VerFactStmt(domFact, nextState)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	return ver.maybeAddSuccessMsg(state, stmt.String(), defStmt.String(), NewExecTrue(""))
}

func (ver *Verifier) verExistSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(stmt)

	propDef := ver.Env.GetExistPropDef(stmt.PropName)
	if propDef == nil {
		// TODO: 如果没声明，应该报错
		return BoolErrToExecRet(false, fmt.Errorf("%s has no definition", stmt))
	}

	uniConMap := map[string]ast.Obj{}
	for i := range existParams {
		uniConMap[propDef.ExistParams[i]] = existParams[i]
	}

	for i := range factParams {
		uniConMap[propDef.DefBody.DefHeader.Params[i]] = factParams[i]
	}

	// given objects are in their param sets
	instParamSets, err := propDef.ExistParamSets.Instantiate(uniConMap)
	if err != nil {
		return BoolErrToExecRet(false, err)
	}
	for i := range instParamSets {
		verRet := ver.VerFactStmt(ast.NewInFactWithFc(existParams[i], instParamSets[i]), state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			execRet := NewExecUnknown("")
			if state.WithMsg {
				msg := fmt.Sprintf("given object %s is not in its param set %s\n", existParams[i], instParamSets[i])
				execRet.AddMsg(msg)
			}
			return execRet
		}
	}

	domFacts, err := propDef.DefBody.DomFacts.InstantiateFact(uniConMap)
	if err != nil {
		return BoolErrToExecRet(false, err)
	}

	iffFacts, err := propDef.DefBody.IffFacts.InstantiateFact(uniConMap)
	if err != nil {
		return BoolErrToExecRet(false, err)
	}

	for _, domFact := range domFacts {
		verRet := ver.VerFactStmt(domFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			execRet := NewExecUnknown("")
			if state.WithMsg {
				msg := fmt.Sprintf("dom fact %s is unknown\n", domFact)
				execRet.AddMsg(msg)
			}
			return execRet
		}
	}

	for _, iffFact := range iffFacts {
		verRet := ver.VerFactStmt(iffFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	return ver.maybeAddSuccessMsg(state, stmt.String(), "by definition", NewExecTrue(""))
}

// func (ver *Verifier) verSpecFactLogicMem(stmt *ast.SpecFactStmt, state *VerState) VerRet {
// 	verRet := ver.verSpecFact_ByLogicMem(stmt, state)
// 	if verRet.IsErr() || verRet.IsTrue() {
// 		return verRet.ToBoolErr()
// 	}
// 	return false, nil
// }

func (ver *Verifier) verSpecFact_UniMem(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	nextState := state.GetAddRound()

	verRet := ver.verSpecFact_InSpecFact_UniMem(stmt, nextState)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return ver.verSpecFact_InLogicExpr_InUniFactMem(stmt, nextState)
}

func (ver *Verifier) verNotTrueEqualFact_BuiltinRules_WithState(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if stmt.IsTrue() {
		return NewExecUnknown("")
	}

	var leftValue, rightValue ast.Obj
	if cmp.IsNumLitObj(stmt.Params[0]) {
		leftValue = stmt.Params[0]
	} else {
		leftValue = ver.Env.GetSymbolSimplifiedValue(stmt.Params[0])
		if leftValue == nil {
			return NewExecUnknown("")
		}
	}
	if cmp.IsNumLitObj(stmt.Params[1]) {
		rightValue = stmt.Params[1]
	} else {
		rightValue = ver.Env.GetSymbolSimplifiedValue(stmt.Params[1])
		if rightValue == nil {
			return NewExecUnknown("")
		}
	}

	_, areEqual, err := cmp.NumLitEqual_ByEval(leftValue, rightValue)
	if err != nil {
		return NewExecErr(err.Error())
	}
	if !areEqual {
		if state != nil {
			return ver.maybeAddSuccessMsg(state, stmt.String(), "builtin rules", NewExecTrue(""))
		}
		return NewExecTrue("")
	}

	// // 如果左右两边能是能被处理的数字
	// areBothNumLit, areEqual, err := cmp.NumLitEqual_ByEval(stmt.Params[0], stmt.Params[1])
	// if err != nil {
	// 	return NewExecErr(err.Error())
	// }
	// if areBothNumLit {
	// 	if !areEqual { // 这里是在证明两边不相等
	// 		ver.processOkMsg(state, stmt.String(), "builtin rules")
	// 		return NewExecTrue("")
	// 	}
	// }

	return NewExecUnknown("")
}

func (ver *Verifier) verNotPureSpecFact_ByDef(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	nextState := state.GetAddRound()

	defStmt := ver.Env.GetPropDef(stmt.PropName)
	if defStmt == nil {
		// 这里可能是因为这个propName是exist prop，所以没有定义
		return NewExecUnknown("")
	}

	if len(defStmt.IffFacts) == 0 {
		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
		return NewExecUnknown("")
	}

	iffToProp := defStmt.IffToPropUniFact()
	paramArrMap := map[string]ast.Obj{}
	for i, param := range stmt.Params {
		paramArrMap[defStmt.DefHeader.Params[i]] = param
	}

	// TODO: ? 这里还需要检查吗？或者说是在这里检查吗？难道prop的关于参数的检查不应该在更顶层的函数里？
	paramSetFacts, err := defStmt.DefHeader.GetInstantiatedParamInParamSetFact(paramArrMap)
	if err != nil {
		return NewExecErr(err.Error())
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
		return NewExecErr(err.Error())
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
			return ver.maybeAddSuccessMsg(state, stmt.String(), defStmt.String(), NewExecTrue(""))
		}
	}

	return NewExecUnknown("")
}
