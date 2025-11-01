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

func (ver *Verifier) checkSpecFactReq(stmt *ast.SpecFactStmt, state *VerState) (VerRet, *VerState) {
	if stmt.NameIs(glob.KeywordIn) {
		ok, err := ver.checkSpecFactReq_InFact_UseBtRules(stmt)
		if err != nil {
			return BoolErrToVerRet(false, err), state
		}

		if ok {
			return BoolErrToVerRet(ok, nil), state
		}

		state, verRet := ver.checkFnsReqAndUpdateReqState(stmt, state)
		return verRet, state
	}

	state, verRet := ver.checkFnsReqAndUpdateReqState(stmt, state)
	return verRet, state
}

// 只验证 1. params都声明了 2. 确实是fn template
// WARNING: 这个函数有严重的问题
func (ver *Verifier) checkSpecFactReq_InFact_UseBtRules(stmt *ast.SpecFactStmt) (bool, error) {
	ok := ver.env.AreAtomsInFcAreDeclared(stmt.Params[0], map[string]struct{}{})
	if !ok {
		return false, fmt.Errorf(env.AtomsInFcNotDeclaredMsg(stmt.Params[0]))
	}

	if _, ok := stmt.Params[1].(*ast.FcFn); !ok {
		return false, nil
	}

	head, ok := stmt.Params[1].(*ast.FcFn).IsFcFn_HasAtomHead_ReturnHead() // WARNING: 这里有问题，因为可能不是fn template，而是 fn(R)R 这种
	// 需要处理 fn(R)R 这种；现在 fn_template 本质上也写成函数形式了
	if ok {
		def := ver.env.GetFnTemplateDef(head)
		if def != nil {
			for _, param := range stmt.Params[1].(*ast.FcFn).Params {
				ok := ver.env.AreAtomsInFcAreDeclared(param, map[string]struct{}{})
				if !ok {
					return false, fmt.Errorf(env.AtomsInFcNotDeclaredMsg(param))
				}
			}
			return true, nil
		} else {
			ok = ver.env.AreAtomsInFcAreDeclared(stmt.Params[1], map[string]struct{}{})
			if !ok {
				return false, fmt.Errorf(env.AtomsInFcNotDeclaredMsg(stmt.Params[1]))
			}
			return true, nil
		}
	} else {
		ok = ver.env.AreAtomsInFcAreDeclared(stmt.Params[1], map[string]struct{}{})
		if !ok {
			return false, fmt.Errorf(env.AtomsInFcNotDeclaredMsg(stmt.Params[1]))
		}

		return true, nil
	}
}

func (ver *Verifier) checkFnsReqAndUpdateReqState(stmt *ast.SpecFactStmt, state *VerState) (*VerState, VerRet) {

	// 1. Check if all atoms in the parameters are declared
	// REMARK
	// TODO： 一层层搜索的时候，会重复检查是否存在，可以优化。比如我要检查 a * f(b) $in R 的时候，我要查 a, f(b) 是否满足条件，就要查 f(b) $in R 是否成立，这时候又查了一遍 f, b 是否存在
	for _, param := range stmt.Params {
		ok := ver.env.AreAtomsInFcAreDeclared(param, map[string]struct{}{})
		if !ok {
			return state, NewVerErr(env.AtomsInFcNotDeclaredMsg(param))
		}
	}

	// TODO: 这里有点问题。应该做的分类是：builtin的 stmt name，如in；以及非builtin的stmt name

	// 2. Check if the parameters satisfy the requirement of the function requirements
	stateNoMsg := state.GetNoMsg()
	for _, param := range stmt.Params {
		verRet := ver.fcSatisfyFnRequirement(param, stateNoMsg)
		if verRet.IsErr() {
			return state, verRet
		}
		if verRet.IsUnknown() {
			return state, BoolErrToVerRet(false, parametersDoNotSatisfyFnReq(param, param))
		}
	}

	// 所有的传入的参数符号 prop 的要求 以及 stmt name 确实是个 prop。这貌似不需要检查，因为每次你得到新的事实时候，已经检查过了
	// 但是最好在这里警告一下用户，如果不满足prop的要求的话，可能出问题

	// state.ReqOk = true
	newState := VerState{state.Round, state.WithMsg, true}
	return &newState, NewVerTrue("")
}

func (ver *Verifier) fcSatisfyFnRequirement(fc ast.Fc, state *VerState) VerRet {
	if _, ok := fc.(ast.FcAtom); ok {
		return NewVerTrue("")
	}
	fcAsFcFn, ok := fc.(*ast.FcFn)
	if !ok {
		return NewVerErr(fmt.Sprintf("%s is not a function", fc))
	}

	// 单独处理特殊的内置prop
	// if isArithmeticFn(fcAsFcFn) {
	// 	return ver.arithmeticFnRequirement(fcAsFcFn, state)
	// } else
	if ast.IsFcFnWithHeadName(fcAsFcFn, glob.KeywordLen) {
		return ver.lenFnRequirement(fcAsFcFn, state)
	} else if ast.IsFnTemplate_FcFn(fcAsFcFn) {
		return NewVerTrue("")
	} else if ver.isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj(fcAsFcFn) {
		return ver.isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj_CheckRequirement(fcAsFcFn, state)
	} else if ast.IsFcAtomAndEqualToStr(fcAsFcFn.FnHead, glob.KeywordSetDefinedByReplacement) {
		return ver.setDefinedByReplacementFnRequirement(fcAsFcFn, state)
		// }
		// else if toCompute, ok := ast.IsFcFnWithCompHeadAndReturnFcToCompute(fcAsFcFn); ok {
		// 	return ver.fcSatisfyFnRequirement(toCompute, state)
	} else {
		// return ver.fcFnSatisfy_FnTemplate_Requirement(fcAsFcFn, state)
		return ver.parasSatisfyFnReq(fcAsFcFn, state)
	}
}

// TODO: 这里需要检查！
func (ver *Verifier) setDefinedByReplacementFnRequirement(fc *ast.FcFn, state *VerState) VerRet {
	if len(fc.Params) != 3 {
		return NewVerErr(fmt.Sprintf("parameters in %s must be 3, %s in %s is not valid", fc.FnHead, fc, fc))
	}

	propName, ok := fc.Params[2].(ast.FcAtom)
	if !ok {
		return NewVerErr(fmt.Sprintf("parameters in %s must be 3, %s in %s is not valid", fc.FnHead, fc, fc))
	}

	forallXOnlyOneYSatisfyGivenProp := ast.GetForallXOnlyOneYSatisfyGivenProp(fc.Params[0], fc.Params[1], propName)

	verRet := ver.VerFactStmt(forallXOnlyOneYSatisfyGivenProp, state)
	return verRet
}

var builtinFunctionNameSetAndCanTakeInAnyObj = map[string]struct{}{
	glob.TupleFcFnHead: {},
}

func (ver *Verifier) isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj(fc *ast.FcFn) bool {
	fcHeadAsAtom, ok := fc.FnHead.(ast.FcAtom)
	if !ok {
		return false
	}

	_, ok = builtinFunctionNameSetAndCanTakeInAnyObj[string(fcHeadAsAtom)]

	return ok
}

func (ver *Verifier) isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj_CheckRequirement(fc *ast.FcFn, state *VerState) VerRet {
	for _, param := range fc.Params {
		verRet := ver.fcSatisfyFnRequirement(param, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return BoolErrToVerRet(false, parametersDoNotSatisfyFnReq(param, fc))
		}
	}

	return NewVerTrue("")
}

func (ver *Verifier) lenFnRequirement(fc *ast.FcFn, state *VerState) VerRet {
	if len(fc.Params) != 1 {
		return NewVerErr(fmt.Sprintf("parameters in %s must be 1, %s in %s is not valid", fc.FnHead, fc, fc))
	}

	verRet := ver.VerFactStmt(ast.NewInFactWithFc(fc.Params[0], ast.FcAtom(glob.KeywordFiniteSet)), state)
	if verRet.IsErr() {
		return NewVerErr(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewVerErr(fmt.Sprintf("parameters in %s must be in set %s, %s in %s is not valid", fc.FnHead, glob.KeywordFiniteSet, fc.Params[0], fc))
	}
	return NewVerTrue("")
}
