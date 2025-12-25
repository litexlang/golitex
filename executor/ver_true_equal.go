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
	env "golitex/environment"
	glob "golitex/glob"
)

// how equality is verified is different from other facts because 1. it is stored differently 2. its transitive and commutative property is automatically used by the verifier
func (ver *Verifier) verTrueEqualFactAndCheckFnReq(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
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

	if verRet := ver.verByReplaceObjInSpecFactWithValueAndCompute(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) verTrueEqualFactMainLogic(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// var verRet ExecRet

	// if checkRequirements && !state.ReqOk {
	// 	// REMARK: 这里 state 更新了： ReqOk 更新到了 true
	// 	if verRet = ver.checkFnsReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
	// 		return NewExecErr(verRet.String())
	// 	}

	// 	state.UpdateReqOkToTrue() // 任何条件下，只要这个fact里面的函数的定义域什么的被检查过了，日后都不再需要检查了

	// 	if !isValidEqualFact(stmt) {
	// 		return NewExecErr(fmt.Sprintf("invalid equal fact: %s", stmt))
	// 	}
	// }

	if verRet := ver.verObjEqual_ByBtRules_SpecMem_LogicMem_UniMem(stmt.Params[0], stmt.Params[1], state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if leftAsFn, ok := stmt.Params[0].(*ast.FnObj); ok {
		if rightAsFn, ok := stmt.Params[1].(*ast.FnObj); ok {
			verRet := ver.verTrueEqualFact_ObjFnEqual_NoCheckRequirements(leftAsFn, rightAsFn, state)
			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		}
	} else {
		return NewEmptyExecUnknown()
	}

	return NewEmptyExecUnknown()
}

func isValidEqualFact(stmt *ast.SpecFactStmt) bool {
	return len(stmt.Params) == 2 && string(stmt.PropName) == glob.KeySymbolEqual
}

func (ver *Verifier) verObjEqual_ByBtRules_SpecMem_LogicMem_UniMem(left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	if verRet := ver.verEqualBuiltin(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualSpecMem(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if !state.isFinalRound() {
		if verRet := ver.verLogicMem_leftToRight_RightToLeft(left, right, state); verRet.IsErr() {
			return verRet
		} else if verRet.IsTrue() {
			return verRet
		}

		if verRet := ver.verEqualUniMem(left, right, state); verRet.IsErr() {
			return verRet
		} else if verRet.IsTrue() {
			return verRet
		}
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) verEqualBuiltin(left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	if verRet := ver.verEqualByBuiltinEval(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualByEitherLeftOrRightIsTuple(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualByLeftAndRightAreSetBuilders(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) verEqualByEitherLeftOrRightIsTuple(left, right ast.Obj, state *VerState) ExecRet {
	if verRet := ver.verEqualRightIsTuple(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualRightIsTuple(right, left, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) verEqualRightIsTuple(left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	if ast.IsTupleObj(right) {
		rightTuple := right.(*ast.FnObj)
		rightLen := len(rightTuple.Params)

		// 查 left 的类型是不是 tuple
		isTupleFact := ast.NewSpecFactStmt(ast.TruePure, glob.KeywordIsTuple, []ast.Obj{left}, glob.BuiltinLine)
		ret := ver.VerFactStmt(isTupleFact, state)
		if ret.IsNotTrue() {
			return NewEmptyExecUnknown()
		}

		// 查 left 的 dim 等于 rightLen 吗
		equalFact := ast.NewEqualFact(ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{left}), ast.Atom(fmt.Sprintf("%d", rightLen)))
		ret = ver.VerFactStmt(equalFact, state)
		if ret.IsNotTrue() {
			return NewEmptyExecUnknown()
		}

		// 查 每一位都相等
		for i := range rightLen {
			leftAtIndex := ast.NewFnObj(ast.Atom(glob.KeywordObjAtIndexOpt), []ast.Obj{left, ast.Atom(fmt.Sprintf("%d", i+1))})
			equalFact := ast.EqualFact(leftAtIndex, rightTuple.Params[i])
			ret = ver.VerFactStmt(equalFact, state)
			if ret.IsNotTrue() {
				return NewEmptyExecUnknown()
			}
		}
	}
	return NewEmptyExecUnknown()
}

func (ver *Verifier) verEqualByBuiltinEval(left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	left = ver.evaluateNonNumberLiteralExpr(left)
	right = ver.evaluateNonNumberLiteralExpr(right)

	ok, msg, err := cmp.CmpBy_Literally_NumLit_PolynomialArith(left, right) // 完全一样
	if err != nil {
		return NewExecErr(err.Error())
	}
	if ok {
		return ver.maybeAddSuccessMsgString(state, fmt.Sprintf("%s = %s", left, right), msg, NewEmptyExecTrue())
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) verEqualSpecMem(left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	// if ver.env.CurMatchProp == nil {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.equalFact_SpecMem_atEnv(curEnv, left, right, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return NewEmptyExecTrue()
		}
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.equalFact_SpecMem_atEnv(&curEnv, left, right, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return NewEmptyExecTrue()
		}
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) equalFact_SpecMem_atEnv(curEnv *env.EnvMemory, left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	nextState := state.GetNoMsg()

	verRet := ver.getEqualObjsAndCmpOneByOne(curEnv, left, right, nextState)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return ver.maybeAddSuccessMsgString(state, fmt.Sprintf("%s = %s", left, right), verRet.String(), verRet)
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) verLogicMem_leftToRight_RightToLeft(left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	equalFact := ast.NewEqualFact(left, right)
	verRet := ver.verSpecFact_ByLogicMem(equalFact, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	equalFactParamReversed, err := equalFact.ReverseSpecFactParamsOrder()
	if err != nil {
		return NewExecErr(err.Error())
	}
	verRet = ver.verSpecFact_ByLogicMem(equalFactParamReversed, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}
	return NewEmptyExecUnknown()
}

func (ver *Verifier) verEqualUniMem(left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	equalFact := ast.NewEqualFact(left, right)
	verRet := ver.verSpecFact_UniMem(equalFact, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	equalFactParamReversed, err := equalFact.ReverseSpecFactParamsOrder()
	if err != nil {
		return NewExecErr(err.Error())
	}
	verRet = ver.verSpecFact_UniMem(equalFactParamReversed, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}
	return NewEmptyExecUnknown()
}

func (ver *Verifier) getEqualObjsAndCmpOneByOne(curEnv *env.EnvMemory, left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	var equalToLeftObjs, equalToRightObjs *[]ast.Obj
	var gotLeftEqualObjs, gotRightEqualObjs bool

	equalToLeftObjs, gotLeftEqualObjs = curEnv.GetEqualObjs(left)
	equalToRightObjs, gotRightEqualObjs = curEnv.GetEqualObjs(right)

	if gotLeftEqualObjs && gotRightEqualObjs {
		if equalToLeftObjs == equalToRightObjs {
			return NewExecTrue(fmt.Sprintf("%s = %s, by either their equality is known, or it is ensured by transitivity of equality.", left, right))
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
				return NewExecTrue(fmt.Sprintf("It is true that:\n%s = %s and %s = %s", equalToLeftObj, right, equalToLeftObj, left))
			}
		}
	}

	if gotRightEqualObjs {
		for _, equalToRightObj := range *equalToRightObjs {
			if verRet := ver.cmpObj_Builtin_Then_Decompose_Spec(equalToRightObj, left, state); verRet.IsErr() {
				return verRet
			} else if verRet.IsTrue() {
				return NewExecTrue(fmt.Sprintf("It is true that\n%s = %s and %s = %s", left, equalToRightObj, equalToRightObj, right))
			}
		}
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) decomposeObjFnsAndCheckEquality(left ast.Obj, right ast.Obj, state *VerState, areEqualObjs func(left ast.Obj, right ast.Obj, state *VerState) ExecRet) ExecRet {
	if leftAsFn, ok := left.(*ast.FnObj); ok {
		if rightAsFn, ok := right.(*ast.FnObj); ok {
			if len(leftAsFn.Params) != len(rightAsFn.Params) {
				return NewEmptyExecUnknown()
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

			return NewExecTrue(fmt.Sprintf("headers and parameters of %s and %s are equal correspondingly", left, right))
		}
	}
	return NewEmptyExecUnknown()
}

func (ver *Verifier) verEqualByLeftAndRightAreSetBuilders(left, right ast.Obj, state *VerState) ExecRet {
	_ = state

	leftSetBuilder := ver.Env.GetSetBuilderEqualToObj(left)
	if leftSetBuilder == nil {
		return NewEmptyExecUnknown()
	}

	rightSetBuilder := ver.Env.GetSetBuilderEqualToObj(right)
	if rightSetBuilder == nil {
		return NewEmptyExecUnknown()
	}
	// 生成一个随机的param，把两个set builder的param都替换成这个随机param
	randomParam := ver.Env.GenerateUndeclaredRandomName()

	leftSetBuilderStruct, err := leftSetBuilder.ToSetBuilderStruct()
	if err != nil {
		return NewExecErr(err.Error())
	}

	rightSetBuilderStruct, err := rightSetBuilder.ToSetBuilderStruct()
	if err != nil {
		return NewExecErr(err.Error())
	}

	if !leftSetBuilderStruct.HasTheSameParentSetAndSpecFactNameAs(rightSetBuilderStruct) {
		return NewEmptyExecUnknown()
	}

	leftSetBuilderStruct, err = leftSetBuilderStruct.ReplaceParamWithNewParam(randomParam)
	if err != nil {
		return NewExecErr(err.Error())
	}

	rightSetBuilderStruct, err = rightSetBuilderStruct.ReplaceParamWithNewParam(randomParam)
	if err != nil {
		return NewExecErr(err.Error())
	}

	if leftSetBuilderStruct.String() == rightSetBuilderStruct.String() {
		return NewExecTrue(fmt.Sprintf("%s = %s, by definition of set builder", left, right))
	}

	return NewEmptyExecUnknown()
}
