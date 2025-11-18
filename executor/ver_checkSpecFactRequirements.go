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
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) checkSpecFactReq(stmt *ast.SpecFactStmt, state *VerState) (ExecRet, *VerState) {
	if stmt.NameIs(glob.KeywordIn) {
		verRet := ver.checkSpecFactReq_InFact_UseBtRules(stmt)
		if verRet.IsErr() {
			return verRet, state
		}
		if verRet.IsTrue() {
			return verRet, state
		}

		state, verRet := ver.checkFnsReqAndUpdateReqState(stmt, state)
		return verRet, state
	}

	state, verRet := ver.checkFnsReqAndUpdateReqState(stmt, state)
	return verRet, state
}

// 只验证 1. params都声明了 2. 确实是fn template
// WARNING: 这个函数有严重的问题
func (ver *Verifier) checkSpecFactReq_InFact_UseBtRules(stmt *ast.SpecFactStmt) ExecRet {
	ok := ver.Env.AreAtomsInFcAreDeclared(stmt.Params[0], map[string]struct{}{})
	if !ok {
		return NewExecErr(env.AtomsInFcNotDeclaredMsg(stmt.Params[0]))
	}

	if _, ok := stmt.Params[1].(*ast.FnObj); !ok {
		return NewExecUnknown("")
	}

	head, ok := stmt.Params[1].(*ast.FnObj).IsFcFn_HasAtomHead_ReturnHead() // WARNING: 这里有问题，因为可能不是fn template，而是 fn(R)R 这种
	// 需要处理 fn(R)R 这种；现在 fn_template 本质上也写成函数形式了
	if ok {
		def := ver.Env.GetFnTemplateDef(head)
		if def != nil {
			for _, param := range stmt.Params[1].(*ast.FnObj).Params {
				ok := ver.Env.AreAtomsInFcAreDeclared(param, map[string]struct{}{})
				if !ok {
					return NewExecErr(env.AtomsInFcNotDeclaredMsg(param))
				}
			}
			return NewExecTrue("")
		} else {
			ok = ver.Env.AreAtomsInFcAreDeclared(stmt.Params[1], map[string]struct{}{})
			if !ok {
				return NewExecErr(env.AtomsInFcNotDeclaredMsg(stmt.Params[1]))
			}
			return NewExecTrue("")
		}
	} else {
		ok = ver.Env.AreAtomsInFcAreDeclared(stmt.Params[1], map[string]struct{}{})
		if !ok {
			return NewExecErr(env.AtomsInFcNotDeclaredMsg(stmt.Params[1]))
		}

		return NewExecTrue("")
	}
}

func (ver *Verifier) checkFnsReqAndUpdateReqState(stmt *ast.SpecFactStmt, state *VerState) (*VerState, ExecRet) {

	// 1. Check if all atoms in the parameters are declared
	// REMARK
	// TODO： 一层层搜索的时候，会重复检查是否存在，可以优化。比如我要检查 a * f(b) $in R 的时候，我要查 a, f(b) 是否满足条件，就要查 f(b) $in R 是否成立，这时候又查了一遍 f, b 是否存在
	for _, param := range stmt.Params {
		ok := ver.Env.AreAtomsInFcAreDeclared(param, map[string]struct{}{})
		if !ok {
			return state, NewExecErr(env.AtomsInFcNotDeclaredMsg(param))
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
	if _, ok := obj.(ast.AtomObj); ok {
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
		return ver.lenFnRequirement(objAsFnObj, state)
	} else if ast.IsFnTemplate_FcFn(objAsFnObj) {
		return NewExecTrue("")
		// }
		// else if ver.isFnObjWithHeadNameBuiltinAndCanTakeInAnyObj(objAsFnObj) {
		// 	return ver.isFnObjWithHeadNameBuiltinAndCanTakeInAnyObj_CheckRequirement(objAsFnObj, state)
	} else if ast.IsAtomObjAndEqualToStr(objAsFnObj.FnHead, glob.KeywordSetDefinedByReplacement) {
		return ver.setDefinedByReplacementFnRequirement(objAsFnObj, state)
		// }
		// else if toCompute, ok := ast.IsFcFnWithCompHeadAndReturnFcToCompute(fcAsFcFn); ok {
		// 	return ver.objSatisfyFnRequirement(toCompute, state)
		// } else if ast.IsAtomObjAndEqualToStr(fcAsFcFn.FnHead, glob.KeywordEval) {
		// 	if len(fcAsFcFn.Params) != 1 {
		// 		return NewExecErr(fmt.Sprintf("%s expect one parameter", glob.KeywordEval))
		// 	}

		// 	return ver.objSatisfyFnRequirement(fcAsFcFn.Params[0], state)
	} else {
		// return ver.fnObjSatisfy_FnTemplate_Requirement(objAsFnObj, state)
		return ver.parasSatisfyFnReq(objAsFnObj, state)
	}
}

// TODO: 这里需要检查！
func (ver *Verifier) setDefinedByReplacementFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) != 3 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 3, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	propName, ok := fnObj.Params[2].(ast.AtomObj)
	if !ok {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 3, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	forallXOnlyOneYSatisfyGivenProp := ast.GetForallXOnlyOneYSatisfyGivenProp(fnObj.Params[0], fnObj.Params[1], propName)

	verRet := ver.VerFactStmt(forallXOnlyOneYSatisfyGivenProp, state)
	return verRet
}

// var builtinFunctionNameSetAndCanTakeInAnyObj = map[string]struct{}{
// 	glob.TupleFcFnHead: {},
// }

// func (ver *Verifier) isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj(fc *ast.FcFn) bool {
// 	_, ok := fc.FnHead.(ast.FcAtom)
// 	if !ok {
// 		return false
// 	}

// _, ok = builtinFunctionNameSetAndCanTakeInAnyObj[string(fcHeadAsAtom)]

// 	return ok
// }

// func (ver *Verifier) isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj_CheckRequirement(fc *ast.FcFn, state *VerState) ExecRet {
// 	for _, param := range fc.Params {
// 		verRet := ver.objSatisfyFnRequirement(param, state)
// 		if verRet.IsErr() || verRet.IsUnknown() {
// 			return BoolErrToExecRet(false, parametersDoNotSatisfyFnReq(param, fc))
// 		}
// 	}

// 	return NewExecTrue("")
// }

func (ver *Verifier) lenFnRequirement(fnObj *ast.FnObj, state *VerState) ExecRet {
	if len(fnObj.Params) != 1 {
		return NewExecErr(fmt.Sprintf("parameters in %s must be 1, %s in %s is not valid", fnObj.FnHead, fnObj, fnObj))
	}

	verRet := ver.VerFactStmt(ast.NewInFactWithFc(fnObj.Params[0], ast.AtomObj(glob.KeywordFiniteSet)), state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(fmt.Sprintf("parameters in %s must be in set %s, %s in %s is not valid", fnObj.FnHead, glob.KeywordFiniteSet, fnObj.Params[0], fnObj))
	}
	return NewExecTrue("")
}
