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

func (ver *Verifier) verEqualMainProcessByBuiltinRules(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	// if verRet := ver.verEqualByUseValuesOfSymbols(left, right, state); verRet.IsErr() || verRet.IsTrue() {
	// 	return verRet
	// }

	// if verRet := ver.verEqualBySetMinusOfListSets(left, right, state); verRet.IsErr() || verRet.IsTrue() {
	// 	return verRet
	// }

	if verRet := ver.verEqualByEitherLeftOrRightIsTuple(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	// if verRet := ver.verEqualByLeftAndRightAreSetBuilders(left, right, state); verRet.IsErr() || verRet.IsTrue() {
	// 	return verRet
	// }

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

// func (ver *Verifier) verEqualByUseValuesOfSymbols(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
// replaced1, left := ver.GetValueOfSymbol(left)
// replaced2, right := ver.GetValueOfSymbol(right)
// if !replaced1 && !replaced2 {
// 	return glob.NewEmptyVerRetUnknown()
// }

// ret := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(left, right) // 完全一样
// if ret.IsErr() {
// 	return ret
// }
// if ret.IsTrue() {
// 	if state.WithMsg {
// 		return ret
// 	}
// 	return glob.NewEmptyVerRetTrue()
// }

// 	return glob.NewEmptyVerRetUnknown()
// }

func (ver *Verifier) verEqualBySpecMem(left ast.Obj, right ast.Obj) *glob.VerRet {
	// if ver.env.CurMatchProp == nil {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.verEqualByEqualSpecMemAtEnv(curEnv, left, right)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.verEqualByEqualSpecMemAtEnv(curEnv, left, right)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.verEqualByEqualSpecMemAtEnv(&curEnv, left, right)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verEqualUniMem(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
	equalFact := ast.NewEqualFact(left, right)
	verRet := ver.verSpecFact_UniMem(equalFact, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	equalFactParamReversed, err := equalFact.ReverseSpecFactParamsOrder()
	if err != nil {
		return glob.NewVerRet(glob.StmtRetTypeError, equalFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}
	verRet = ver.verSpecFact_UniMem(equalFactParamReversed, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}
	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verEqualByEqualSpecMemAtEnv(curEnv *env.EnvMemory, left ast.Obj, right ast.Obj) *glob.VerRet {
	equalToLeftObjs, gotLeftEqualObjs := curEnv.GetEqualObjs(left)
	equalToRightObjs, gotRightEqualObjs := curEnv.GetEqualObjs(right)

	if gotLeftEqualObjs && gotRightEqualObjs {
		if equalToLeftObjs == equalToRightObjs {
			return glob.NewVerRet(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", left, right), glob.BuiltinLine0, []string{"by either their equality is known, or it is ensured by transitivity of equality."})
		}
	}

	if verRet := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(left, right); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if gotLeftEqualObjs {
		for _, equalToLeftObj := range *equalToLeftObjs {
			if verRet := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(equalToLeftObj, right); verRet.IsErr() {
				return verRet
			} else if verRet.IsTrue() {
				return glob.NewVerRet(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", equalToLeftObj, right), glob.BuiltinLine0, []string{fmt.Sprintf("It is known that:\n%s = %s and %s = %s", equalToLeftObj, right, equalToLeftObj, left)})
			}
		}
	}

	if gotRightEqualObjs {
		for _, equalToRightObj := range *equalToRightObjs {
			if verRet := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(equalToRightObj, left); verRet.IsErr() {
				return verRet
			} else if verRet.IsTrue() {
				return glob.NewVerRet(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", left, equalToRightObj), glob.BuiltinLine0, []string{fmt.Sprintf("It is known that\n%s = %s and %s = %s", left, equalToRightObj, equalToRightObj, right)})
			}
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

// func (ver *Verifier) verEqualByLeftAndRightAreSetBuilders(left, right ast.Obj, state *VerState) *glob.VerRet {
// _ = state

// leftSetBuilder := ver.Env.GetSetBuilderEqualToObj(left)
// if leftSetBuilder == nil {
// 	return glob.NewEmptyVerRetUnknown()
// }

// rightSetBuilder := ver.Env.GetSetBuilderEqualToObj(right)
// if rightSetBuilder == nil {
// 	return glob.NewEmptyVerRetUnknown()
// }
// // 生成一个随机的param，把两个set builder的param都替换成这个随机param
// randomParam := ver.Env.GenerateUnusedRandomName()

// leftSetBuilderStruct, err := leftSetBuilder.ToSetBuilderStruct()
// if err != nil {
// 	return glob.NewVerRet(glob.StmtRetTypeError, left.String(), glob.BuiltinLine0, []string{err.Error()})
// }

// rightSetBuilderStruct, err := rightSetBuilder.ToSetBuilderStruct()
// if err != nil {
// 	return glob.NewVerRet(glob.StmtRetTypeError, right.String(), glob.BuiltinLine0, []string{err.Error()})
// }

// if !leftSetBuilderStruct.HasTheSameParentSetAndSpecFactNameAs(rightSetBuilderStruct) {
// 	return glob.NewEmptyVerRetUnknown()
// }

// leftSetBuilderStruct, err = leftSetBuilderStruct.ReplaceParamWithNewParam(randomParam)
// if err != nil {
// 	return glob.NewVerRet(glob.StmtRetTypeError, left.String(), glob.BuiltinLine0, []string{err.Error()})
// }

// rightSetBuilderStruct, err = rightSetBuilderStruct.ReplaceParamWithNewParam(randomParam)
// if err != nil {
// 	return glob.NewVerRet(glob.StmtRetTypeError, right.String(), glob.BuiltinLine0, []string{err.Error()})
// }

// if leftSetBuilderStruct.String() == rightSetBuilderStruct.String() {
// 	return glob.NewVerRet(glob.StmtRetTypeTrue, fmt.Sprintf("%s = %s", left, right), glob.BuiltinLine0, []string{"by definition of set builder"})
// }

// return glob.NewEmptyVerRetUnknown()
// }

// verEqualBySetMinusOfListSets verifies equality when left is set_minus(list_set1, list_set2) and right is a list_set
// It computes set_minus by removing elements from list_set1 that are in list_set2
// func (ver *Verifier) verEqualBySetMinusOfListSets(left ast.Obj, right ast.Obj, state *VerState) *glob.VerRet {
// 	// Check if left is a set_minus function call
// 	leftFnObj, ok := left.(*ast.FnObj)
// 	if !ok {
// 		return glob.NewEmptyVerRetUnknown()
// 	}

// 	if !ast.IsFn_WithHeadName(leftFnObj, glob.KeywordSetMinus) {
// 		return glob.NewEmptyVerRetUnknown()
// 	}

// 	// Check that set_minus has 2 parameters
// 	if len(leftFnObj.Params) != 2 {
// 		return glob.NewEmptyVerRetUnknown()
// 	}

// 	// Get the actual list_set objects (they might be equal to list_sets rather than being list_sets directly)
// 	leftListSet1 := ver.Env.GetListSetEqualToObj(leftFnObj.Params[0])
// 	if leftListSet1 == nil {
// 		return glob.NewEmptyVerRetUnknown()
// 	}

// 	leftListSet2 := ver.Env.GetListSetEqualToObj(leftFnObj.Params[1])
// 	if leftListSet2 == nil {
// 		return glob.NewEmptyVerRetUnknown()
// 	}

// 	// Check if right is a list_set
// 	rightListSet := ver.Env.GetListSetEqualToObj(right)
// 	if rightListSet == nil {
// 		return glob.NewEmptyVerRetUnknown()
// 	}

// 	// Convert to FnObj to access parameters
// 	listSet1FnObj, ok := leftListSet1.(*ast.FnObj)
// 	if !ok {
// 		return glob.NewEmptyVerRetUnknown()
// 	}

// 	listSet2FnObj, ok := leftListSet2.(*ast.FnObj)
// 	if !ok {
// 		return glob.NewEmptyVerRetUnknown()
// 	}

// 	rightListSetFnObj, ok := rightListSet.(*ast.FnObj)
// 	if !ok {
// 		return glob.NewEmptyVerRetUnknown()
// 	}

// 	// right 里的东西都在 listSet1 里，但不在 listSet2 里
// 	for _, elem := range rightListSetFnObj.Params {
// 		equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{elem, listSet1FnObj}, glob.BuiltinLine0)
// 		verRet := ver.VerFactStmt(equalFact, state)
// 		if verRet.IsTrue() {
// 			// 要能证明 forall item in right => not item $in listSet2
// 			for _, itemInListSet2 := range listSet2FnObj.Params {
// 				notEqual := ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{itemInListSet2, elem}, glob.BuiltinLine0)
// 				verRet := ver.VerFactStmt(notEqual, state)
// 				if verRet.IsNotTrue() {
// 					return glob.NewEmptyVerRetUnknown()
// 				}
// 			}
// 		} else {
// 			return glob.NewEmptyVerRetUnknown()
// 		}
// 	}

// 	// listSet1 里的东西都在 right 里，不在right里就在 listSet2 里
// 	for _, elem := range listSet1FnObj.Params {
// 		equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{elem, rightListSetFnObj}, glob.BuiltinLine0)
// 		verRet := ver.VerFactStmt(equalFact, state)
// 		if verRet.IsTrue() {
// 			continue
// 		}

// 		equalFact = ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{elem, listSet2FnObj}, glob.BuiltinLine0)
// 		verRet = ver.VerFactStmt(equalFact, state)
// 		if verRet.IsNotTrue() {
// 			return glob.NewEmptyVerRetUnknown()
// 		}
// 	}

// 	return glob.NewEmptyVerRetTrue()
// }
