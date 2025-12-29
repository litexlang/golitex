// Copyright Jiachen Shen.
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

func (ver *Verifier) verSpecFactNotInFormOfTrueEqualAndCheckFnReq(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if !state.ReqOk {
		if verRet := ver.checkFnsReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		state.UpdateReqOkToTrue()
	}

	ret := ver.verSpecFactThatIsNotTrueEqualFact_UseCommutativity(stmt, state)
	if ret.IsTrue() || ret.IsErr() {
		return ret
	}

	ret = ver.verSpecialFactInSpecialWays(stmt, state)
	if ret.IsTrue() || ret.IsErr() {
		return ret
	}

	return glob.UnknownRet(stmt.String())
}

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_UseCommutativity(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeySymbolEqual) {
		return ver.verTrueEqualFactAndCheckFnReq(stmt, state.CopyAndReqOkToFalse())
	}

	if verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	// if ver.env.IsCommutativeProp(stmt) || (stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.FalsePure) {
	if ver.Env.IsCommutativeProp(stmt) {
		reverseParamsOrderStmt, err := stmt.ReverseParameterOrder()
		if err != nil {
			return glob.ErrRet(err.Error())
		}
		if verRet := ver.verSpecFactThatIsNotTrueEqualFact_UseTransitivity(reverseParamsOrderStmt, state); verRet.IsTrue() || verRet.IsErr() {
			return verRet
		}
	}

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_UseTransitivity(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	verRet := ver.verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(stmt, state)
	if verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	if stmt.FactType == ast.TruePure && ver.Env.IsTransitiveProp(string(stmt.PropName)) {
		relatedObjSlice := ver.Env.GetRelatedObjSliceOfTransitiveProp(string(stmt.PropName), stmt.Params[0])
		if len(relatedObjSlice) == 0 {
			return glob.NewEmptyStmtUnknown()
		}

		for _, relatedObj := range relatedObjSlice {
			relatedObjStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.PropName), []ast.Obj{relatedObj, stmt.Params[1]}, stmt.Line)
			verRet := ver.verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(relatedObjStmt, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				msg := fmt.Sprintf("%s is true by %s is a transitive prop and %s is true", stmt.String(), string(stmt.PropName), relatedObjStmt.String())
				return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyStmtTrue())
			}
		}
	}

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verSpecFactThatIsNotTrueEqualFact_WithoutTransitive(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	// replace the params with the values 来证明
	// 比如 $q(x, y) 证明不出来，但可能 $q(1, 2) 证明出来了，如果x=1,y=2的话。这里会用到 1. 如果x和y本来就是数学表达式，那就计算 2. 如果 x和y之前存过数值，那就用之前存过的值。
	replaced, newStmt := ver.Env.ReplaceObjInSpecFactWithValue(stmt)
	if replaced {
		verRet := ver.verSpecFactThatIsNotTrueEqualFactMainLogic(newStmt, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			msg := fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String())
			return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyStmtTrue())
		}
	}

	verRet := ver.verSpecFactThatIsNotTrueEqualFactMainLogic(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyStmtUnknown()
}

// TODO: 其实 specFact 是等号的时候，还是会访问到这个函数。
// WARNING: 其实 specFact 是等号的时候，还是会访问到这个函数。所以这个函数的命名是有问题的
// WARNING: 需要重构整个架构，把验证的逻辑屡屡顺。Litex是ATP的话，那就必须要告诉用户我Auto的过程是什么样的
func (ver *Verifier) verSpecFactThatIsNotTrueEqualFactMainLogic(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	// var verRet *glob.GlobRet

	// if !state.ReqOk {
	// 	if verRet = ver.checkFnsReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
	// 		return verRet
	// 	}

	// 	state.UpdateReqOkToTrue()
	// }
	return ver.verSpecFactStepByStep(stmt, state)
}

func (ver *Verifier) verSpecFactStepByStep(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if verRet := ver.verSpecFactByBuiltinRules(stmt, state); verRet.IsErr() || verRet.IsTrue() {
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

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verSpecFact_ByDEF(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if stmt.IsPureFact() {
		if !stmt.IsTrue() {
			return ver.verNotPureSpecFact_ByDef(stmt, state)
		}

		return ver.verPureSpecFact_ByDefinition(stmt, state)
	}

	if stmt.IsExist_St_Fact() {
		return ver.verExistSpecFact_ByDefinition(stmt, state)
	}

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verPureSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	// nextState := state.GetAddRound()

	curDefStmt := ver.Env.GetPropDef(stmt.PropName)
	// defStmt := curDefStmt
	if curDefStmt == nil {
		// 这里可能是因为这个propName是exist prop，所以没有定义
		return glob.NewEmptyStmtUnknown()
	}

	if len(curDefStmt.IffFactsOrNil) == 0 {
		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
		return glob.NewEmptyStmtUnknown()
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
		return glob.ErrRet(err.Error())
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
		return glob.ErrRet(err.Error())
	}
	// prove all domFacts are true
	for _, domFact := range instantiatedIffToProp.DomFacts {
		// verRet := ver.VerFactStmt(domFact, nextState)
		verRet := ver.VerFactStmt(domFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	return ver.maybeAddSuccessMsgString(state, stmt.String(), defStmt.String(), glob.NewEmptyStmtTrue())
}

func (ver *Verifier) verExistSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(stmt)

	propDef := ver.Env.GetExistPropDef(stmt.PropName)
	if propDef == nil {
		// TODO: 如果没声明，应该报错
		return glob.ErrRet(fmt.Sprintf("%s has no definition", stmt.PropName))
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
		return glob.ErrRet(err.Error())
	}
	for i := range instParamSets {
		verRet := ver.VerFactStmt(ast.NewInFactWithObj(existParams[i], instParamSets[i]), state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			execRet := glob.NewEmptyStmtUnknown()
			if state.WithMsg {
				msg := fmt.Sprintf("given object %s is not in its param set %s\n", existParams[i], instParamSets[i])
				execRet.AddUnknown(msg)
			}
			return execRet
		}
	}

	domFacts, err := propDef.DefBody.DomFactsOrNil.InstantiateFact(uniConMap)
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	iffFacts, err := propDef.DefBody.IffFactsOrNil.InstantiateFact(uniConMap)
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	for _, domFact := range domFacts {
		verRet := ver.VerFactStmt(domFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			execRet := glob.NewEmptyStmtUnknown()
			if state.WithMsg {
				msg := fmt.Sprintf("dom fact %s is unknown\n", domFact)
				execRet.AddUnknown(msg)
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

	return ver.maybeAddSuccessMsgString(state, stmt.String(), "by definition", glob.NewEmptyStmtTrue())
}

// func (ver *Verifier) verSpecFactLogicMem(stmt *ast.SpecFactStmt, state *VerState) VerRet {
// 	verRet := ver.verSpecFact_ByLogicMem(stmt, state)
// 	if verRet.IsErr() || verRet.IsTrue() {
// 		return verRet.ToBoolErr()
// 	}
// 	return false, nil
// }

func (ver *Verifier) verSpecFact_UniMem(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	nextState := state.GetAddRound()

	verRet := ver.verSpecFact_InSpecFact_UniMem(stmt, nextState)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return ver.verSpecFact_InLogicExpr_InUniFactMem(stmt, nextState)
}

func (ver *Verifier) verNotTrueEqualFact_BuiltinRules_WithState(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if stmt.IsTrue() {
		return glob.NewEmptyStmtUnknown()
	}

	// 如果右侧是0，且左边是减号，那就证明左边这两个东西不等
	// if ret := ver.whenRightIsZeroAndLeftFnIsMinus(stmt, state); ret.IsNotUnknown() {
	// 	return ret
	// }

	var leftValue, rightValue ast.Obj
	if cmp.IsNumExprLitObj(stmt.Params[0]) {
		leftValue = stmt.Params[0]
	} else {
		leftValue = ver.Env.GetSymbolSimplifiedValue(stmt.Params[0])
		if leftValue == nil {
			return glob.NewEmptyStmtUnknown()
		}
	}
	if cmp.IsNumExprLitObj(stmt.Params[1]) {
		rightValue = stmt.Params[1]
	} else {
		rightValue = ver.Env.GetSymbolSimplifiedValue(stmt.Params[1])
		if rightValue == nil {
			return glob.NewEmptyStmtUnknown()
		}
	}

	_, areEqual, err := cmp.NumLitEqual_ByEval(leftValue, rightValue)
	if err != nil {
		return glob.ErrRet(err.Error())
	}
	if !areEqual {
		if state != nil {
			return ver.maybeAddSuccessMsgString(state, stmt.String(), "builtin rules", glob.NewEmptyStmtTrue())
		}
		return glob.NewEmptyStmtTrue()
	}

	// // 如果左右两边能是能被处理的数字
	// areBothNumLit, areEqual, err := cmp.NumLitEqual_ByEval(stmt.Params[0], stmt.Params[1])
	// if err != nil {
	// 	return glob.ErrRet(err.Error())
	// }
	// if areBothNumLit {
	// 	if !areEqual { // 这里是在证明两边不相等
	// 		ver.processOkMsg(state, stmt.String(), "builtin rules")
	// 		return NewExecEmptyTrue()
	// 	}
	// }

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verIsCartByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	// 如果参数数量是1，且参数的函数名是cart，那自动成立
	if len(stmt.Params) == 1 {
		if cartObj, ok := stmt.Params[0].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cartObj.FnHead, glob.KeywordCart) {
			return ver.maybeAddSuccessMsgString(state, stmt.String(), "definition", glob.NewEmptyStmtTrue())
		}
	}
	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verNotPureSpecFact_ByDef(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	nextState := state.GetAddRound()

	defStmt := ver.Env.GetPropDef(stmt.PropName)
	if defStmt == nil {
		// 这里可能是因为这个propName是exist prop，所以没有定义
		return glob.NewEmptyStmtUnknown()
	}

	if len(defStmt.IffFactsOrNil) == 0 {
		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
		return glob.NewEmptyStmtUnknown()
	}

	iffToProp := defStmt.IffToPropUniFact()
	paramArrMap := map[string]ast.Obj{}
	for i, param := range stmt.Params {
		paramArrMap[defStmt.DefHeader.Params[i]] = param
	}

	// TODO: ? 这里还需要检查吗？或者说是在这里检查吗？难道prop的关于参数的检查不应该在更顶层的函数里？
	paramSetFacts, err := defStmt.DefHeader.GetInstantiatedParamInParamSetFact(paramArrMap)
	if err != nil {
		return glob.ErrRet(err.Error())
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
		return glob.ErrRet(err.Error())
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
			return ver.maybeAddSuccessMsgString(state, stmt.String(), defStmt.String(), glob.NewEmptyStmtTrue())
		}
	}

	return glob.NewEmptyStmtUnknown()
}

// $equal_tuple(left, right, dim)
func (ver *Verifier) verEqualTupleByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if len(stmt.Params) != 3 {
		return glob.ErrRet(fmt.Sprintf("equal_tuple should have 3 params, but got %d", len(stmt.Params)))
	}

	left := stmt.Params[0]
	right := stmt.Params[1]
	dim := stmt.Params[2]

	// 1. 证明 left 是 is_tuple
	isTupleLeftFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{left}, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isTupleLeftFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return glob.UnknownRet(fmt.Sprintf("cannot verify that %s is a tuple", left))
	}

	// 2. 证明 right 是 is_tuple
	isTupleRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{right}, glob.BuiltinLine0)
	verRet = ver.VerFactStmt(isTupleRightFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return glob.UnknownRet(fmt.Sprintf("cannot verify that %s is a tuple", right))
	}

	// 3. 证明 dim(left) = dim
	dimLeftFn := ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{left})
	dimLeftEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{dimLeftFn, dim}, glob.BuiltinLine0)
	verRet = ver.VerFactStmt(dimLeftEqualFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return glob.UnknownRet(fmt.Sprintf("cannot verify that dim(%s) = %s", left, dim))
	}

	// 4. 证明 dim(right) = dim
	dimRightFn := ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{right})
	dimRightEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{dimRightFn, dim}, glob.BuiltinLine0)
	verRet = ver.VerFactStmt(dimRightEqualFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return glob.UnknownRet(fmt.Sprintf("cannot verify that dim(%s) = %s", right, dim))
	}

	// 5. 获取 dim 的数值，用于枚举
	dimValue, ok := ast.ToInt(dim)
	if !ok {
		// 如果 dim 不是直接的数字，尝试从环境中获取值
		if symbolValue := ver.Env.GetSymbolSimplifiedValue(dim); symbolValue != nil {
			dimValue, ok = ast.ToInt(symbolValue)
		}
		// 如果方法1失败，尝试从相等事实中获取
		if !ok {
			if equalObjs, gotEqualObjs := ver.Env.GetEqualObjs(dim); gotEqualObjs && equalObjs != nil {
				for _, equalObj := range *equalObjs {
					if dimValue, ok = ast.ToInt(equalObj); ok {
						break
					}
				}
			}
		}
		if !ok {
			return glob.ErrRet(fmt.Sprintf("cannot determine integer value of dim %s", dim))
		}
	}

	// 6. 用枚举方法一位位证明 equal: left[i] = right[i] for i = 1 to dim
	for i := 1; i <= dimValue; i++ {
		indexObj := ast.Atom(fmt.Sprintf("%d", i))

		// 创建索引操作: left[i] 和 right[i]
		leftIndexed := ast.NewFnObj(ast.Atom(glob.KeywordObjAtIndexOpt), []ast.Obj{left, indexObj})
		rightIndexed := ast.NewFnObj(ast.Atom(glob.KeywordObjAtIndexOpt), []ast.Obj{right, indexObj})

		// 创建相等事实: left[i] = right[i]
		indexEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{leftIndexed, rightIndexed}, glob.BuiltinLine0)
		verRet := ver.VerFactStmt(indexEqualFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return glob.UnknownRet(fmt.Sprintf("cannot verify that %s[%d] = %s[%d]", left, i, right, i))
		}
	}

	msg := fmt.Sprintf("verified %s and %s are tuples with dim = %s, and each element %s[i] = %s[i] for i = 1 to %d", left, right, dim, left, right, dimValue)
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyStmtTrue())
}
