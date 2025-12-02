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
	glob "golitex/glob"
)

func (ver *Verifier) checkFnsReqAndUpdateReqState(stmt *ast.SpecFactStmt, state *VerState) (*VerState, ExecRet) {

	// 1. Check if all atoms in the parameters are declared
	// REMARK
	// TODO： 一层层搜索的时候，会重复检查是否存在，可以优化。比如我要检查 a * f(b) $in R 的时候，我要查 a, f(b) 是否满足条件，就要查 f(b) $in R 是否成立，这时候又查了一遍 f, b 是否存在
	for _, param := range stmt.Params {
		ret := ver.Env.AreAtomsInFcAreDeclared(param, map[string]struct{}{})
		if ret.IsErr() {
			return state, NewExecErr(ret.String())
		}
	}

	// TODO: 这里有点问题。应该做的分类是：builtin的 stmt name，如in；以及非builtin的stmt name

	// 2. Check if the parameters satisfy the requirement of the function requirements
	stateNoMsg := state.GetNoMsg()
	for _, param := range stmt.Params {
		verRet := ver.objSatisfyFnRequirement(param, stateNoMsg)
		if verRet.IsErr() {
			return state, verRet
		}
		if verRet.IsUnknown() {
			return state, BoolErrToExecRet(false, parametersDoNotSatisfyFnReq(param, param))
		}
	}

	// 所有的传入的参数符号 prop 的要求 以及 stmt name 确实是个 prop。这貌似不需要检查，因为每次你得到新的事实时候，已经检查过了
	// 但是最好在这里警告一下用户，如果不满足prop的要求的话，可能出问题

	// state.ReqOk = true
	newState := VerState{state.Round, state.WithMsg, true}
	return &newState, NewExecTrue("")
}

func (ver *Verifier) objSatisfyFnRequirement(obj ast.Obj, state *VerState) ExecRet {
	if _, ok := obj.(ast.Atom); ok {
		return NewExecTrue("")
	}
	objAsFnObj, ok := obj.(*ast.FnObj)
	if !ok {
		return NewExecErr(fmt.Sprintf("%s is not a function", obj))
	}

	// 单独处理特殊的内置prop
	// if isArithmeticFn(objAsFnObj) {
	// 	return ver.arithmeticFnRequirement(objAsFnObj, state)
	// } else
	if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordCount) {
		return ver.countFnRequirement(objAsFnObj, state)
	} else if ast.IsFnTemplate_FcFn(objAsFnObj) {
		return NewExecTrue("")
	} else if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordCart) {
		return ver.cartFnRequirement(objAsFnObj, state)
	} else if ast.IsTupleFnObj(objAsFnObj) {
		if len(objAsFnObj.Params) < 2 {
			return NewExecErr(fmt.Sprintf("parameters in %s must be at least 2, %s in %s is not valid", objAsFnObj.FnHead, objAsFnObj, objAsFnObj))
		}

		for _, param := range objAsFnObj.Params {
			if !ObjIsNotSet(param) {
				return NewExecErr(fmt.Sprintf("parameters in %s must not be set", objAsFnObj.String()))
			}
		}
		return NewExecTrue("")
	} else if ast.IsIndexOptFnObj(objAsFnObj) {
		return ver.indexOptFnRequirement(objAsFnObj, state)
	} else if objAsFnObj.FnHead.String() == glob.KeywordProj {
		return ver.parasSatisfyProjReq(objAsFnObj, state)
	} else if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordSetDim) {
		return ver.setDimFnRequirement(objAsFnObj, state)
	} else if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordDim) {
		return ver.dimFnRequirement(objAsFnObj, state)
	} else {
		return ver.parasSatisfyFnReq(objAsFnObj, state)
	}
}

func (ver *Verifier) dimFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) != 1 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 1, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}
	// 检查是否是 tuple
	isTupleFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{fnObj.Params[0]}, glob.InnerGenLine)
	verRet := ver.VerFactStmt(isTupleFact, state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("%s is not unknown", isTupleFact))
	}
	return NewExecTrue("")
}

func (ver *Verifier) setDimFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) != 1 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 1, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	verRet := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fnObj.Params[0]}, glob.InnerGenLine), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("parameters in %s must be sets, %s in %s is not valid", fnObj.FnHead, fnObj.Params[0], fnObj))
	}
	return NewExecTrue("")
}

func (ver *Verifier) parasSatisfyProjReq(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) != 2 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 2, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	// x is cart
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fnObj.Params[0]}, glob.InnerGenLine)
	verRet := ver.VerFactStmt(isCartFact, state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("%s is not unknown", isCartFact))
	}

	// index >= 1
	verRet = ver.VerFactStmt(ast.NewInFactWithFc(fnObj.Params[1], ast.Atom(glob.KeywordNPos)), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("index in %s must be N_pos, %s in %s is not valid", fnObj, fnObj.Params[1], fnObj))
	}

	// index <= set_dim(x)
	verRet = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fnObj.Params[1], ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{fnObj.Params[0]})}, glob.InnerGenLine), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	} else if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("index in %s must be <= set_dim(%s), %s in %s is not valid", fnObj, fnObj.Params[0], fnObj.Params[1], fnObj))
	}

	return NewExecTrue("")
}

// // TODO: 这里需要检查！
// func (ver *Verifier) setDefinedByReplacementFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
// 	if len(fnObj.Params) != 3 {
// 		return NewExecErr(fmt.Sprintf("parameters in %s must be 3, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
// 	}

// 	propName, ok := fnObj.Params[2].(ast.AtomObj)
// 	if !ok {
// 		return NewExecErr(fmt.Sprintf("parameters in %s must be 3, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
// 	}

// 	forallXOnlyOneYSatisfyGivenProp := ast.GetForallXOnlyOneYSatisfyGivenProp(fnObj.Params[0], fnObj.Params[1], propName)

// 	verRet := ver.VerFactStmt(forallXOnlyOneYSatisfyGivenProp, state)
// 	return verRet
// }

func (ver *Verifier) countFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) != 1 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 1, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	verRet := ver.VerFactStmt(ast.NewInFactWithFc(fnObj.Params[0], ast.Atom(glob.KeywordFiniteSet)), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("parameters in %s must be in set %s, %s in %s is not valid", fnObj.FnHead, glob.KeywordFiniteSet, fnObj.Params[0], fnObj))
	}
	return NewExecTrue("")
}

func (ver *Verifier) cartFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) < 2 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be at least 2, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	// 验证所有的参数都是集合
	for _, param := range fnObj.Params {
		verRet := ver.VerFactStmt(ast.NewInFactWithFc(param, ast.Atom(glob.KeywordSet)), state)
		if verRet.IsErr() {
			return NewExecErr(verRet.String())
		}
		if verRet.IsUnknown() {
			return NewExecErr(fmt.Sprintf("parameters in %s must be sets, %s in %s is not valid", fnObj.FnHead, param, glob.KeywordSet))
		}
	}
	return NewExecTrue("")
}

func (ver *Verifier) indexOptFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	_ = state

	// [] 操作需要两个参数：obj 和 index
	if len(fnObj.Params) != 2 {
		return NewExecErr(fmt.Sprintf("[] operator requires 2 parameters, got %d in %s", len(fnObj.Params), fnObj))
	}

	obj := fnObj.Params[0]
	indexObj := fnObj.Params[1]

	// 检查是不是正整数N_pos

	verRet := ver.VerFactStmt(ast.NewInFactWithFc(indexObj, ast.Atom(glob.KeywordNPos)), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("index in %s must be N_pos, %s in %s is not valid", fnObj, indexObj, fnObj))
	}

	// 如果 index 本来就是数字，那就换成数字；如果不是数字，那换成这个symbol
	// 的值
	var index int
	var ok bool
	// 首先尝试直接转换为整数
	index, ok = ast.ToInt(indexObj)
	if !ok {
		// 如果不是数字，尝试从环境中获取值
		// 方法1: 尝试获取符号的简化值
		if symbolValue := ver.Env.GetSymbolSimplifiedValue(indexObj); symbolValue != nil {
			index, ok = ast.ToInt(symbolValue)
		}
		// 方法2: 如果方法1失败，尝试从相等事实中获取
		if !ok {
			if equalFcs, gotEqualFcs := ver.Env.GetEqualFcs(indexObj); gotEqualFcs && equalFcs != nil {
				for _, equalFc := range *equalFcs {
					if index, ok = ast.ToInt(equalFc); ok {
						break
					}
				}
			}
		}
		// 如果仍然无法获取整数值，返回错误
		if !ok {
			return NewExecErr(fmt.Sprintf("cannot determine integer value of index %s in %s", indexObj, fnObj))
		}
	}

	// 情况1: obj 本身就是一个 tuple，比如 (1,2)[1]
	if objAsTuple, ok := obj.(*ast.FnObj); ok && ast.IsTupleFnObj(objAsTuple) {
		if index > len(objAsTuple.Params) {
			return NewExecErr(fmt.Sprintf("index %d in %s is out of range, tuple has %d elements", index, fnObj, len(objAsTuple.Params)))
		}
		return NewExecTrue("")
	}

	// 情况3: 检查 dim(obj) 的值
	// 索引必须 >= 1 且 <= dim(obj)
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{obj})
	equalFcs, ok := ver.Env.GetEqualFcs(dimFn)
	if ok && equalFcs != nil {
		// 查找 dim 的数值
		for _, equalFc := range *equalFcs {
			if dimValue, ok := ast.ToInt(equalFc); ok {
				// 检查 index >= 1 且 index <= dim(obj)
				if index > dimValue {
					return NewExecErr(fmt.Sprintf("index %d in %s is out of range, dim(%s) = %d", index, fnObj, obj, dimValue))
				}
				// 如果找到了 dim 值并且 index 在范围内，返回成功
				return NewExecTrue("")
			}
		}
	}

	return NewExecTrue("")
}
