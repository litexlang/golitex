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
	env "golitex/environment"
	glob "golitex/glob"
)

// how equality is verified is different from other facts because 1. it is stored differently 2. its transitive and commutative property is automatically used by the verifier
func (ver *Verifier) verTrueEqualFactAndCheckFnReq(stmt ast.SpecificFactStmt, state *VerState) *glob.VerRet {
	if !state.ReqOk {
		if verRet := ver.checkFnsReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		state.UpdateReqOkToTrue()
	}

	if verRet := ver.verByReplaceObjInSpecFactWithValue(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	if verRet := ver.verTrueEqualFactMainLogic(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	// if verRet := ver.verByReplaceObjInSpecFactWithValueAndCompute(stmt, state); verRet.IsTrue() || verRet.IsErr() {
	// 	return verRet
	// }

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verTrueEqualFactMainLogic(stmt ast.SpecificFactStmt, state *VerState) *glob.VerRet {

	asStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	if verRet := ver.verObjEqual_ByBtRules_SpecMem_LogicMem_UniMem(asStmt.Params[0], asStmt.Params[1], state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if leftAsFn, ok := asStmt.Params[0].(*ast.FnObj); ok {
		if rightAsFn, ok := asStmt.Params[1].(*ast.FnObj); ok {
			verRet := ver.verTrueEqualFact_ObjFnEqual_NoCheckRequirements(leftAsFn, rightAsFn, state)
			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		}
	} else {
		return glob.NewEmptyVerRetUnknown()
	}

	return glob.NewEmptyVerRetUnknown()
}

// extractValParam extracts the parameter from val(x), returns x and true if it's a val call
func (ver *Verifier) extractValParam(obj ast.Obj) (ast.Obj, bool) {
	if fnObj, ok := obj.(*ast.FnObj); ok {
		if ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeywordVal) && len(fnObj.Params) == 1 {
			return fnObj.Params[0], true
		}
	}
	return nil, false
}

// func isValidEqualFact(stmt *ast.SpecFactStmt) bool {
// 	return len(stmt.Params) == 2 && string(stmt.PropName) == glob.KeySymbolEqual
// }

func (ver *Verifier) verObjEqual_ByBtRules_SpecMem_LogicMem_UniMem(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	// val(x) = y is equivalent to x = y (val is handled in ReplaceObjInSpecFactWithValue)
	if leftVal, ok := ver.extractValParam(left); ok {
		verRet := ver.verObjEqual_ByBtRules_SpecMem_LogicMem_UniMem(leftVal, right, state)
		if verRet.IsTrue() || verRet.IsErr() {
			return verRet
		}
	}
	if rightVal, ok := ver.extractValParam(right); ok {
		verRet := ver.verObjEqual_ByBtRules_SpecMem_LogicMem_UniMem(left, rightVal, state)
		if verRet.IsTrue() || verRet.IsErr() {
			return verRet
		}
	}

	if verRet := ver.verEqualBuiltin(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualSpecMem(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if !state.isFinalRound() {
		// if verRet := ver.verLogicMem_leftToRight_RightToLeft(left, right, state); verRet.IsErr() {
		// 	return verRet
		// } else if verRet.IsTrue() {
		// 	return verRet
		// }

		if verRet := ver.verEqualUniMem(left, right, state); verRet.IsErr() {
			return verRet
		} else if verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verEqualBuiltin(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	if verRet := ver.verEqualByBuiltinEval(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualBySetMinusOfListSets(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualByEitherLeftOrRightIsTuple(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualByLeftAndRightAreSetBuilders(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verEqualByEitherLeftOrRightIsTuple(left, right ast.Obj, state *VerState) *glob.VerRet {
	if verRet := ver.verEqualRightIsTuple(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualRightIsTuple(right, left, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verEqualRightIsTuple(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	if ast.IsTupleObj(right) {
		rightTuple := right.(*ast.FnObj)
		rightLen := len(rightTuple.Params)

		// 查 left 的类型是不是 tuple
		isTupleFact := ast.NewPureSpecificFactStmt(true, glob.KeywordIsTuple, []ast.Obj{left}, glob.BuiltinLine0)
		ret := ver.VerFactStmt(isTupleFact, state)
		if ret.IsNotTrue() {
			return glob.NewEmptyVerRetUnknown()
		}

		// 查 left 的 dim 等于 rightLen 吗
		equalFact := ast.NewEqualFact(ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{left}), ast.Atom(fmt.Sprintf("%d", rightLen)))
		ret = ver.VerFactStmt(equalFact, state)
		if ret.IsNotTrue() {
			return glob.NewEmptyVerRetUnknown()
		}

		// 查 每一位都相等
		for i := range rightLen {
			leftAtIndex := ast.NewFnObj(ast.Atom(glob.KeywordObjAtIndexOpt), []ast.Obj{left, ast.Atom(fmt.Sprintf("%d", i+1))})
			equalFact := ast.EqualFact(leftAtIndex, rightTuple.Params[i])
			ret = ver.VerFactStmt(equalFact, state)
			if ret.IsNotTrue() {
				return glob.NewEmptyVerRetUnknown()
			}
		}
	}
	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verEqualByBuiltinEval(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	left = ver.evaluateNonNumberLiteralExpr(left)
	right = ver.evaluateNonNumberLiteralExpr(right)

	ok, msg, err := cmp.CmpBy_Literally_NumLit_PolynomialArith(left, right) // 完全一样
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, fmt.Sprintf("%s = %s", left, right), glob.BuiltinLine0, []string{err.Error()})
	}
	if ok {
		if state.WithMsg {
			return glob.NewVerMsg(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s by evaluation", left, right), glob.BuiltinLine0, []string{msg})
		}
		return glob.NewEmptyVerRetTrue()
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verEqualSpecMem(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	// if ver.env.CurMatchProp == nil {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.equalFact_SpecMem_atEnv(curEnv, left, right, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.equalFact_SpecMem_atEnv(curEnv, left, right, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.equalFact_SpecMem_atEnv(&curEnv, left, right, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) equalFact_SpecMem_atEnv(curEnv *env.EnvMemory, left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	nextState := state.GetNoMsg()

	verRet := ver.getEqualObjsAndCmpOneByOne(curEnv, left, right, nextState)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		if state.WithMsg {
			return glob.NewVerMsg(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", left, right), glob.BuiltinLine0, verRet.VerifyMsgs)
		}
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

// func (ver *Verifier) verLogicMem_leftToRight_RightToLeft(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
// 	equalFact := ast.NewEqualFact(left, right)
// 	verRet := ver.verSpecFact_ByLogicMem(equalFact, state)
// 	if verRet.IsErr() || verRet.IsTrue() {
// 		return verRet
// 	}

// 	equalFactParamReversed, err := equalFact.ReverseSpecFactParamsOrder()
// 	if err != nil {
// 		return glob.NewVerMsg(glob.StmtRetTypeError, equalFact.String(), glob.BuiltinLine0, []string{err.Error()})
// 	}
// 	verRet = ver.verSpecFact_ByLogicMem(equalFactParamReversed, state)
// 	if verRet.IsErr() || verRet.IsTrue() {
// 		return verRet
// 	}
// 	return glob.NewEmptyVerRetUnknown()
// }

func (ver *Verifier) verEqualUniMem(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	equalFact := ast.NewEqualFact(left, right)
	verRet := ver.verSpecFact_UniMem(equalFact, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	equalFactParamReversed, err := equalFact.ReverseSpecFactParamsOrder()
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, equalFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}
	verRet = ver.verSpecFact_UniMem(equalFactParamReversed, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}
	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) getEqualObjsAndCmpOneByOne(curEnv *env.EnvMemory, left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	var equalToLeftObjs, equalToRightObjs *[]ast.Obj
	var gotLeftEqualObjs, gotRightEqualObjs bool

	equalToLeftObjs, gotLeftEqualObjs = curEnv.GetEqualObjs(left)
	equalToRightObjs, gotRightEqualObjs = curEnv.GetEqualObjs(right)

	if gotLeftEqualObjs && gotRightEqualObjs {
		if equalToLeftObjs == equalToRightObjs {
			return glob.NewVerMsg(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", left, right), glob.BuiltinLine0, []string{"by either their equality is known, or it is ensured by transitivity of equality."})
		}
	}

	if verRet := ver.cmpObj_Builtin_Then_Decompose_Spec(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if gotLeftEqualObjs {
		for _, equalToLeftObj := range *equalToLeftObjs {
			if verRet := ver.cmpObj_Builtin_Then_Decompose_Spec(equalToLeftObj, right, state); verRet.IsErr() {
				return verRet
			} else if verRet.IsTrue() {
				return glob.NewVerMsg(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", equalToLeftObj, right), glob.BuiltinLine0, []string{fmt.Sprintf("It is true that:\n%s = %s and %s = %s", equalToLeftObj, right, equalToLeftObj, left)})
			}
		}
	}

	if gotRightEqualObjs {
		for _, equalToRightObj := range *equalToRightObjs {
			if verRet := ver.cmpObj_Builtin_Then_Decompose_Spec(equalToRightObj, left, state); verRet.IsErr() {
				return verRet
			} else if verRet.IsTrue() {
				return glob.NewVerMsg(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", left, equalToRightObj), glob.BuiltinLine0, []string{fmt.Sprintf("It is true that\n%s = %s and %s = %s", left, equalToRightObj, equalToRightObj, right)})
			}
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) decomposeObjFnsAndCheckEquality(left ast.Obj, right ast.Obj, state *VerState, areEqualObjs func(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet) *glob.VerRet {
	if leftAsFn, ok := left.(*ast.FnObj); ok {
		if rightAsFn, ok := right.(*ast.FnObj); ok {
			if len(leftAsFn.Params) != len(rightAsFn.Params) {
				return glob.NewEmptyVerRetUnknown()
			}

			// compare head
			verRet := areEqualObjs(leftAsFn.FnHead, rightAsFn.FnHead, state)
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
			// compare params
			for i := range leftAsFn.Params {
				verRet := areEqualObjs(leftAsFn.Params[i], rightAsFn.Params[i], state)
				if verRet.IsErr() || verRet.IsUnknown() {
					return verRet
				}
			}

			return glob.NewVerMsg(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", left, right), glob.BuiltinLine0, []string{fmt.Sprintf("headers and parameters of %s and %s are equal correspondingly", left, right)})
		}
	}
	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verEqualByLeftAndRightAreSetBuilders(left, right ast.Obj, state *VerState) *glob.VerRet {
	_ = state

	leftSetBuilder := ver.Env.GetSetBuilderEqualToObj(left)
	if leftSetBuilder == nil {
		return glob.NewEmptyVerRetUnknown()
	}

	rightSetBuilder := ver.Env.GetSetBuilderEqualToObj(right)
	if rightSetBuilder == nil {
		return glob.NewEmptyVerRetUnknown()
	}
	// 生成一个随机的param，把两个set builder的param都替换成这个随机param
	randomParam := ver.Env.GenerateUndeclaredRandomName()

	leftSetBuilderStruct, err := leftSetBuilder.ToSetBuilderStruct()
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, left.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	rightSetBuilderStruct, err := rightSetBuilder.ToSetBuilderStruct()
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, right.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	if !leftSetBuilderStruct.HasTheSameParentSetAndSpecFactNameAs(rightSetBuilderStruct) {
		return glob.NewEmptyVerRetUnknown()
	}

	leftSetBuilderStruct, err = leftSetBuilderStruct.ReplaceParamWithNewParam(randomParam)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, left.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	rightSetBuilderStruct, err = rightSetBuilderStruct.ReplaceParamWithNewParam(randomParam)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, right.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	if leftSetBuilderStruct.String() == rightSetBuilderStruct.String() {
		return glob.NewVerMsg(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", left, right), glob.BuiltinLine0, []string{"by definition of set builder"})
	}

	return glob.NewEmptyVerRetUnknown()
}

// verEqualBySetMinusOfListSets verifies equality when left is set_minus(list_set1, list_set2) and right is a list_set
// It computes set_minus by removing elements from list_set1 that are in list_set2
func (ver *Verifier) verEqualBySetMinusOfListSets(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	// Check if left is a set_minus function call
	leftFnObj, ok := left.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	if !ast.IsFn_WithHeadName(leftFnObj, glob.KeywordSetMinus) {
		return glob.NewEmptyVerRetUnknown()
	}

	// Check that set_minus has 2 parameters
	if len(leftFnObj.Params) != 2 {
		return glob.NewEmptyVerRetUnknown()
	}

	// Get the actual list_set objects (they might be equal to list_sets rather than being list_sets directly)
	leftListSet1 := ver.Env.GetListSetEqualToObj(leftFnObj.Params[0])
	if leftListSet1 == nil {
		return glob.NewEmptyVerRetUnknown()
	}

	leftListSet2 := ver.Env.GetListSetEqualToObj(leftFnObj.Params[1])
	if leftListSet2 == nil {
		return glob.NewEmptyVerRetUnknown()
	}

	// Check if right is a list_set
	rightListSet := ver.Env.GetListSetEqualToObj(right)
	if rightListSet == nil {
		return glob.NewEmptyVerRetUnknown()
	}

	// Convert to FnObj to access parameters
	listSet1FnObj, ok := leftListSet1.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	listSet2FnObj, ok := leftListSet2.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	rightListSetFnObj, ok := rightListSet.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	// right 里的东西都在 listSet1 里，但不在 listSet2 里
	for _, elem := range rightListSetFnObj.Params {
		equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{elem, listSet1FnObj}, glob.BuiltinLine0)
		verRet := ver.VerFactStmt(equalFact, state)
		if verRet.IsTrue() {
			// 要能证明 forall item in right => not item $in listSet2
			for _, itemInListSet2 := range listSet2FnObj.Params {
				notEqual := ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{itemInListSet2, elem}, glob.BuiltinLine0)
				verRet := ver.VerFactStmt(notEqual, state)
				if verRet.IsNotTrue() {
					return glob.NewEmptyVerRetUnknown()
				}
			}
		} else {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	// listSet1 里的东西都在 right 里，不在right里就在 listSet2 里
	for _, elem := range listSet1FnObj.Params {
		equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{elem, rightListSetFnObj}, glob.BuiltinLine0)
		verRet := ver.VerFactStmt(equalFact, state)
		if verRet.IsTrue() {
			continue
		}

		equalFact = ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{elem, listSet2FnObj}, glob.BuiltinLine0)
		verRet = ver.VerFactStmt(equalFact, state)
		if verRet.IsNotTrue() {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	return glob.NewEmptyVerRetTrue()
}
