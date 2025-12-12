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

func (ver *Verifier) checkFnsReqAndUpdateReqState(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// TODO: 这里有点问题。应该做的分类是：builtin的 stmt name，如in；以及非builtin的stmt name

	// 2. Check if the parameters satisfy the requirement of the function requirements
	stateNoMsg := state.GetNoMsg()
	for _, param := range stmt.Params {
		verRet := ver.objIsDefinedAtomOrIsFnSatisfyItsReq(param, stateNoMsg)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return NewExecErrWithMsgs(verRet.GetMsgs())
		}
	}

	// 所有的传入的参数符号 prop 的要求 以及 stmt name 确实是个 prop。这貌似不需要检查，因为每次你得到新的事实时候，已经检查过了
	// 但是最好在这里警告一下用户，如果不满足prop的要求的话，可能出问题

	// state.ReqOk = true
	// newState := VerState{state.Round, state.WithMsg, true}
	return NewEmptyExecTrue()
}

func (ver *Verifier) objIsDefinedAtomOrIsFnSatisfyItsReq(obj ast.Obj, state *VerState) ExecRet {
	if atom, ok := obj.(ast.Atom); ok {
		if ver.Env.AreAtomsInObjDefined(atom, map[string]struct{}{}).IsNotTrue() {
			return NewExecErr(fmt.Sprintf("%s is not defined", atom))
		} else {
			return NewEmptyExecTrue()
		}
	}

	objAsFnObj, ok := obj.(*ast.FnObj)
	if !ok {
		return NewExecErr(fmt.Sprintf("%s is not a function", obj))
	}

	if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordCount) {
		return ver.countFnRequirement(objAsFnObj, state)
	} else if ast.IsFnTemplate_ObjFn(objAsFnObj) {
		return NewEmptyExecTrue()
	} else if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordCart) {
		return ver.cartFnRequirement(objAsFnObj, state)
	} else if ast.IsTupleFnObj(objAsFnObj) {
		return ver.tupleFnReq(objAsFnObj, state)
	} else if ast.IsIndexOptFnObj(objAsFnObj) {
		return ver.indexOptFnRequirement(objAsFnObj, state)
	} else if objAsFnObj.FnHead.String() == glob.KeywordProj {
		return ver.parasSatisfyProjReq(objAsFnObj, state)
	} else if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordSetDim) {
		return ver.setDimFnRequirement(objAsFnObj, state)
	} else if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordDim) {
		return ver.dimFnRequirement(objAsFnObj, state)
	} else if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordListSet) {
		return ver.listSetFnRequirement(objAsFnObj, state)
	} else if ast.IsFn_WithHeadName(objAsFnObj, glob.KeywordSetBuilder) {
		return ver.SetBuilderFnRequirement(objAsFnObj, state)
	} else {
		return ver.parasSatisfyFnReq(objAsFnObj, state)
	}
}

// TODO: 非常缺乏检查。因为这里的验证非常麻烦，{}里包括了事实，而事实里有fn，所以需要检查fn行不行
func (ver *Verifier) SetBuilderFnRequirement(objAsFnObj *ast.FnObj, state *VerState) ExecRet {
	ver.newEnv(ver.Env)
	defer ver.deleteEnvAndRetainMsg()

	// Parse set builder struct to check facts
	setBuilderStruct, err := objAsFnObj.ToSetBuilderStruct()
	if err != nil {
		return NewExecErr(fmt.Sprintf("failed to parse set builder: %s", err))
	}

	// parent is a set
	verRet := ver.VerFactStmt(ast.NewInFactWithObj(setBuilderStruct.ParentSet, ast.Atom(glob.KeywordSet)), state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("parent of %s must be a set, %s in %s is not valid", objAsFnObj, setBuilderStruct.ParentSet, objAsFnObj))
	}

	// parent is ok
	ret := ver.objIsDefinedAtomOrIsFnSatisfyItsReq(setBuilderStruct.ParentSet, state)
	if ret.IsErr() {
		return ret
	}
	if ret.IsUnknown() {
		return NewExecErr(fmt.Sprintf("parent of %s must be a set, %s in %s is not valid", objAsFnObj, setBuilderStruct.ParentSet, objAsFnObj))
	}

	// 如果param在母环境里已经声明过了，那就把整个obj里的所有的param全部改成新的
	globRet := ver.Env.IsAtomDeclared(ast.Atom(setBuilderStruct.Param), map[string]struct{}{})
	if globRet.IsTrue() {
		// 把这个param替换成从来没见过的东西
		setBuilderStruct = ver.replaceParamWithUndeclaredRandomName(setBuilderStruct)
	}

	// 声明一下param
	ver.Env.DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(ast.NewDefLetStmt(
		[]string{setBuilderStruct.Param},
		[]ast.Obj{setBuilderStruct.ParentSet},
		[]ast.FactStmt{},
		glob.BuiltinLine,
	))

	// Check all parameters in facts satisfy fn requirement
	for _, fact := range setBuilderStruct.Facts {
		// Check propName
		verRet := ver.objIsDefinedAtomOrIsFnSatisfyItsReq(fact.PropName, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return NewExecErr(fmt.Sprintf("prop name %s in set builder must be an atom or function", fact.PropName))
		}

		// Check all params in the fact
		for _, param := range fact.Params {
			verRet := ver.objIsDefinedAtomOrIsFnSatisfyItsReq(param, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsUnknown() {
				return NewExecErr(fmt.Sprintf("parameter %s in set builder fact must be an atom or function", param))
			}
		}
	}

	return NewEmptyExecTrue()
}

func (ver *Verifier) listSetFnRequirement(objAsFnObj *ast.FnObj, state *VerState) ExecRet {
	// 所有参数都是$in list set
	for _, param := range objAsFnObj.Params {
		verRet := ver.VerFactStmt(ast.NewInFactWithObj(param, ast.Atom(glob.KeywordSet)), state)
		if verRet.IsErr() {
			return NewExecErr(verRet.String())
		}
		if verRet.IsUnknown() {
			return NewExecErr(fmt.Sprintf("parameters in %s must be sets, %s in %s is not valid", objAsFnObj.FnHead, param, objAsFnObj))
		}
	}

	// 所有参数互相不相等
	for i := range len(objAsFnObj.Params) {
		for j := i + 1; j < len(objAsFnObj.Params); j++ {
			fact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{objAsFnObj.Params[i], objAsFnObj.Params[j]}, glob.BuiltinLine)
			verRet := ver.VerFactStmt(fact, state)
			if verRet.IsErr() {
				return NewExecErr(verRet.String())
			}
			if verRet.IsUnknown() {
				return NewExecErr(fmt.Sprintf("parameters in set must be different from one another, inequality of %s and %s in %s is unknown", objAsFnObj.Params[i], objAsFnObj.Params[j], objAsFnObj))
			}
		}
	}

	return NewEmptyExecTrue()
}

func (ver *Verifier) tupleFnReq(objAsFnObj *ast.FnObj, state *VerState) ExecRet {
	if len(objAsFnObj.Params) < 2 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be at least 2, %s in %s is not valid", objAsFnObj.FnHead, objAsFnObj, objAsFnObj))
	}

	_ = state

	for _, param := range objAsFnObj.Params {
		if !ObjIsNotSet(param) {
			return NewExecErr(fmt.Sprintf("parameters in %s must not be set", objAsFnObj.String()))
		}
	}
	return NewEmptyExecTrue()
}

func (ver *Verifier) dimFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) != 1 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 1, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}
	// 检查是否是 tuple
	isTupleFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{fnObj.Params[0]}, glob.BuiltinLine)
	verRet := ver.VerFactStmt(isTupleFact, state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("%s is unknown", isTupleFact))
	}
	return NewEmptyExecTrue()
}

func (ver *Verifier) setDimFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) != 1 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 1, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	verRet := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fnObj.Params[0]}, glob.BuiltinLine), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("parameters in %s must be sets, %s in %s is not valid", fnObj.FnHead, fnObj.Params[0], fnObj))
	}
	return NewEmptyExecTrue()
}

func (ver *Verifier) parasSatisfyProjReq(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) != 2 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 2, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	// x is cart
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fnObj.Params[0]}, glob.BuiltinLine)
	verRet := ver.VerFactStmt(isCartFact, state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("%s is unknown", isCartFact))
	}

	// index >= 1
	verRet = ver.VerFactStmt(ast.NewInFactWithObj(fnObj.Params[1], ast.Atom(glob.KeywordNPos)), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("index in %s must be N_pos, %s in %s is not valid", fnObj, fnObj.Params[1], fnObj))
	}

	// index <= set_dim(x)
	verRet = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{fnObj.Params[1], ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{fnObj.Params[0]})}, glob.BuiltinLine), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	} else if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("index in %s must be <= set_dim(%s), %s in %s is not valid", fnObj, fnObj.Params[0], fnObj.Params[1], fnObj))
	}

	return NewEmptyExecTrue()
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

	verRet := ver.VerFactStmt(ast.NewInFactWithObj(fnObj.Params[0], ast.Atom(glob.KeywordFiniteSet)), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("parameters in %s must be in set %s, %s in %s is not valid", fnObj.FnHead, glob.KeywordFiniteSet, fnObj.Params[0], fnObj))
	}
	return NewEmptyExecTrue()
}

func (ver *Verifier) cartFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) < 2 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be at least 2, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	// 验证所有的参数都是集合
	for _, param := range fnObj.Params {
		verRet := ver.VerFactStmt(ast.NewInFactWithObj(param, ast.Atom(glob.KeywordSet)), state)
		if verRet.IsErr() {
			return NewExecErr(verRet.String())
		}
		if verRet.IsUnknown() {
			return NewExecErr(fmt.Sprintf("parameters in %s must be sets, %s in %s is not valid", fnObj.FnHead, param, glob.KeywordSet))
		}
	}
	return NewEmptyExecTrue()
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

	verRet := ver.VerFactStmt(ast.NewInFactWithObj(indexObj, ast.Atom(glob.KeywordNPos)), state)
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
			if equalObjs, gotEqualObjs := ver.Env.GetEqualObjs(indexObj); gotEqualObjs && equalObjs != nil {
				for _, equalObj := range *equalObjs {
					if index, ok = ast.ToInt(equalObj); ok {
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
		return NewEmptyExecTrue()
	}

	// 情况3: 检查 dim(obj) 的值
	// 索引必须 >= 1 且 <= dim(obj)
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{obj})
	equalObjs, ok := ver.Env.GetEqualObjs(dimFn)
	if ok && equalObjs != nil {
		// 查找 dim 的数值
		for _, equalObj := range *equalObjs {
			if dimValue, ok := ast.ToInt(equalObj); ok {
				// 检查 index >= 1 且 index <= dim(obj)
				if index > dimValue {
					return NewExecErr(fmt.Sprintf("index %d in %s is out of range, dim(%s) = %d", index, fnObj, obj, dimValue))
				}
				// 如果找到了 dim 值并且 index 在范围内，返回成功
				return NewEmptyExecTrue()
			}
		}
	}

	return NewEmptyExecTrue()
}

func (ver *Verifier) replaceParamWithUndeclaredRandomName(setBuilderStruct *ast.SetBuilderStruct) *ast.SetBuilderStruct {
	oldParam := ast.Atom(setBuilderStruct.Param)

	// Generate a new random undeclared name
	newParamName := ver.Env.GenerateUndeclaredRandomName()
	newParam := ast.Atom(newParamName)

	// Replace param in all facts
	newFacts := make(ast.SpecFactPtrSlice, len(setBuilderStruct.Facts))
	for i, fact := range setBuilderStruct.Facts {
		// Replace param in propName
		newPropName := fact.PropName.ReplaceObj(oldParam, newParam).(ast.Atom)

		// Replace param in fact params
		newFactParams := make([]ast.Obj, len(fact.Params))
		for j, param := range fact.Params {
			newFactParams[j] = param.ReplaceObj(oldParam, newParam)
		}

		// Create new fact with replaced param
		newFacts[i] = ast.NewSpecFactStmt(fact.TypeEnum, newPropName, newFactParams, fact.Line)
	}

	return &ast.SetBuilderStruct{
		Param:     newParamName,
		ParentSet: setBuilderStruct.ParentSet, // parent set 不变
		Facts:     newFacts,
	}
}
