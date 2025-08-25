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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) checkSpecFactReq(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if stmt.NameIs(glob.KeywordIn) {
		ok, err := ver.checkSpecFactReq_InFact_UseBtRules(stmt)
		if err != nil {
			return false, err
		}

		if ok {
			return ok, nil
		}

		return ver.checkSpecFactRequirements(stmt, state)
	}

	return ver.checkSpecFactRequirements(stmt, state)
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
		_, ok := ver.env.GetFnTemplateDef(head)
		if ok {
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

func (ver *Verifier) checkSpecFactRequirements(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {

	// 1. Check if all atoms in the parameters are declared
	// REMARK
	// TODO： 一层层搜索的时候，会重复检查是否存在，可以优化。比如我要检查 a * f(b) $in R 的时候，我要查 a, f(b) 是否满足条件，就要查 f(b) $in R 是否成立，这时候又查了一遍 f, b 是否存在
	for _, param := range stmt.Params {
		ok := ver.env.AreAtomsInFcAreDeclared(param, map[string]struct{}{})
		if !ok {
			return false, fmt.Errorf(env.AtomsInFcNotDeclaredMsg(param))
		}
	}

	// TODO: 这里有点问题。应该做的分类是：builtin的 stmt name，如in；以及非builtin的stmt name

	// 2. Check if the parameters satisfy the requirement of the function requirements
	stateNoMsg := state.GetNoMsg()
	for _, param := range stmt.Params {
		ok, err := ver.fcSatisfyFnRequirement(param, stateNoMsg)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, parametersDoNotSatisfyFnReq(param, param)
		}
	}

	// 所有的传入的参数符号 prop 的要求 以及 stmt name 确实是个 prop。这貌似不需要检查，因为每次你得到新的事实时候，已经检查过了
	// 但是最好在这里警告一下用户，如果不满足prop的要求的话，可能出问题

	state.ReqOk = true
	return true, nil
}

func (ver *Verifier) fcSatisfyFnRequirement(fc ast.Fc, state *VerState) (bool, error) {
	if _, ok := fc.(ast.FcAtom); ok {
		return true, nil
	}
	fcAsFcFn, ok := fc.(*ast.FcFn)
	if !ok {
		return false, fmt.Errorf("%s is not a function", fc)
	}

	// 单独处理特殊的内置prop
	// if isArithmeticFn(fcAsFcFn) {
	// 	return ver.arithmeticFnRequirement(fcAsFcFn, state)
	// } else
	if ast.IsFcFnWithHeadName(fcAsFcFn, glob.KeywordLen) {
		return ver.lenFnRequirement(fcAsFcFn, state)
	} else if ast.IsFnTemplate_FcFn(fcAsFcFn) {
		return true, nil
	} else if ver.isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj(fcAsFcFn) {
		return ver.isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj_CheckRequirement(fcAsFcFn, state)
	} else if ast.IsFcAtomAndEqualToStr(fcAsFcFn.FnHead, glob.KeywordSetDefinedByReplacement) {
		return ver.setDefinedByReplacementFnRequirement(fcAsFcFn, state)
	} else {
		return ver.fcFnSatisfy_FnTemplate_Requirement(fcAsFcFn, state)
	}
}

func (ver *Verifier) fcFnSatisfy_FnTemplate_Requirement(fc ast.Fc, state *VerState) (bool, error) {
	var err error

	asFcFn, ok := fc.(*ast.FcFn)
	if !ok {
		return false, fmt.Errorf("%s is not a function", fc)
	}

	fnTemplateSlice, ok := ver.GetFnTemplateSliceTheFnIsIn(asFcFn.FnHead)
	if !ok {
		return false, nil
	}

	for i := len(fnTemplateSlice) - 1; i >= 0; i-- {
		if fnTemplateSlice[i].FnTemplateStmt != nil {
			ok, err = ver.fcFnParamsSatisfyFnTemplateNoNameRequirement(asFcFn, fnTemplateSlice[i].FnTemplateStmt, state)
			if err != nil {
				return false, err
			}
			if ok {
				return true, nil
			}
		} else {
			if fnTemplateSlice[i].InFcFn == nil {
				return false, nil
			}

			everythingOK := true

			if len(asFcFn.Params) != len(fnTemplateSlice[i].InFcFn.Params) {
				return false, nil
			}

			for i := range asFcFn.Params {
				ok, err = ver.VerFactStmt(ast.NewInFactWithFc(asFcFn.Params[i], fnTemplateSlice[i].InFcFn.FnHead.(*ast.FcFn).Params[i]), state)
				if err != nil {
					return false, err
				}
				if !ok {
					everythingOK = false
					break
				}
			}

			if everythingOK {
				return true, nil
			}

		}
	}

	return false, nil
}

func (ver *Verifier) fcFnParamsSatisfyFnTemplateNoNameRequirement(fcFn *ast.FcFn, templateOfFn *ast.FnTStruct, state *VerState) (bool, error) {
	if len(fcFn.Params) != len(templateOfFn.Params) {
		return false, fmt.Errorf("parameters in %s must be %d, %s in %s is not valid", fcFn.FnHead, len(templateOfFn.Params), fcFn, fcFn)
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range fcFn.Params {
		uniMap[templateOfFn.Params[i]] = param
	}

	paramSets, instantiatedDomFacts, _, _, err := templateOfFn.InstantiateFnTWithoutChangingTName(uniMap)
	if err != nil {
		return false, err
	}

	for i, paramSet := range paramSets {
		ok, err := ver.VerFactStmt(ast.NewInFactWithFc(fcFn.Params[i], paramSet), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	for _, domFact := range instantiatedDomFacts {
		ok, err := ver.VerFactStmt(domFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}

// TODO: 这里需要检查！
func (ver *Verifier) setDefinedByReplacementFnRequirement(fc *ast.FcFn, state *VerState) (bool, error) {
	if len(fc.Params) != 3 {
		return false, fmt.Errorf("parameters in %s must be 3, %s in %s is not valid", fc.FnHead, fc, fc)
	}

	propName, ok := fc.Params[2].(ast.FcAtom)
	if !ok {
		return false, fmt.Errorf("parameters in %s must be 3, %s in %s is not valid", fc.FnHead, fc, fc)
	}

	forallXOnlyOneYSatisfyGivenProp := ast.GetForallXOnlyOneYSatisfyGivenProp(fc.Params[0], fc.Params[1], propName)
	ok, err := ver.VerFactStmt(forallXOnlyOneYSatisfyGivenProp, state)
	if err != nil {
		return false, err
	}

	return ok, nil
}

var builtinFunctionNameSetAndCanTakeInAnyObj = map[string]struct{}{
	glob.TupleFcFnHead:     {},
	glob.KeywordSetProduct: {},
	// glob.TupleAtOp:         {}, // 之后改成必须要是 $in 某个set_product才行，暂时先这样；同时传入的index需要是int
	// glob.KeywordProj: {},
}

func (ver *Verifier) isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj(fc *ast.FcFn) bool {
	fcHeadAsAtom, ok := fc.FnHead.(ast.FcAtom)
	if !ok {
		return false
	}

	_, ok = builtinFunctionNameSetAndCanTakeInAnyObj[string(fcHeadAsAtom)]

	return ok
}

func (ver *Verifier) isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj_CheckRequirement(fc *ast.FcFn, state *VerState) (bool, error) {
	for _, param := range fc.Params {
		ok, err := ver.fcSatisfyFnRequirement(param, state)
		if err != nil || !ok {
			return false, parametersDoNotSatisfyFnReq(param, fc)
		}
	}

	return true, nil
}

func (ver *Verifier) lenFnRequirement(fc *ast.FcFn, state *VerState) (bool, error) {
	if len(fc.Params) != 1 {
		return false, fmt.Errorf("parameters in %s must be 1, %s in %s is not valid", fc.FnHead, fc, fc)
	}

	ok, err := ver.VerFactStmt(ast.NewInFactWithFc(fc.Params[0], ast.FcAtom(glob.KeywordFiniteSet)), state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, fmt.Errorf("parameters in %s must be in set %s, %s in %s is not valid", fc.FnHead, glob.KeywordFiniteSet, fc.Params[0], fc)
	}

	return true, nil
}

func (ver *Verifier) GetFnTemplateSliceTheFnIsIn(fnName ast.Fc) ([]env.FnInFnTTMemItem, bool) {
	fnInFnTTMenItemSlice, ok := ver.env.GetFnTemplateSliceTheFnIsInFromEnv(fnName.String())
	if ok {
		return fnInFnTTMenItemSlice, true
	}

	fnNameAsFcFn, ok := fnName.(*ast.FcFn)
	if !ok {
		return nil, false
	}

	// 先只考虑这个 fnNameAsFcFn 是 f() 形式，而不是 f()() 这种
	head, ok := fnNameAsFcFn.FnHead.(ast.FcAtom)
	if !ok {
		return nil, false
	}

	// 得到 head 的定义
	// templateFnIsIn, ok := ver.env.Parent.GetLatestFnTT_GivenNameIsIn(head.String())
	// if !ok {
	// 	return nil, false
	// }
	fnInFnTTMemItemSlice, ok := ver.env.FnInFnTemplateFactsMem[head.String()]
	if !ok {
		return nil, false
	}
	fnInFnTTMemItem := fnInFnTTMemItemSlice[len(fnInFnTTMemItemSlice)-1]
	// var ret = env.FnInFnTTMemItem{nil, nil}
	ret := env.MakeFnInFnTTMemItem(nil, nil)

	// var templateFnIsIn = &env.FnInFnTTMemItem{nil, nil}
	templateFnIsIn := env.MakeFnInFnTTMemItem(nil, nil)
	var err error
	if fnInFnTTMemItem.InFcFn != nil {
		uniMap := map[string]ast.Fc{}
		for i, param := range fnInFnTTMemItem.InFcFn.Params {
			uniMap[fnInFnTTMemItem.FnTemplateStmt.Params[i]] = param
		}

		InFcFn, err := fnInFnTTMemItem.InFcFn.Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		templateFnIsIn.InFcFn = InFcFn.(*ast.FcFn)

		retFcFn, err := templateFnIsIn.InFcFn.Params[0].Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		retFcFnAsFcFn, ok := retFcFn.(*ast.FcFn)
		if !ok {
			return nil, false
		}

		if ast.IsFnTemplate_FcFn(retFcFnAsFcFn) {
			ret.InFcFn = retFcFn.(*ast.FcFn)
		} else {
			// 不知道如何处理返回值是 template 的情况
			return nil, false
		}
	} else {
		uniMap := map[string]ast.Fc{}
		for i, param := range fnInFnTTMemItem.FnTemplateStmt.Params {
			uniMap[param] = fnNameAsFcFn.Params[i]
		}

		template, err := fnInFnTTMemItem.FnTemplateStmt.Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		templateFnIsIn.FnTemplateStmt = template

		retTemplate, err := templateFnIsIn.FnTemplateStmt.RetSet.Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		retTemplateFcFn, ok := retTemplate.(*ast.FcFn)
		if !ok {
			return nil, false
		}

		if ast.IsFnTemplate_FcFn(retTemplateFcFn) {
			ret.InFcFn = retTemplateFcFn
		} else {
			// 不知道如何处理返回值是 template 的情况
			return nil, false
		}
	}

	// 参数满足 fnTemplateDef 的参数要求
	ok, err = ver.paramsSatisfyFnTemplateParamReq(fnNameAsFcFn, &templateFnIsIn)
	if err != nil {
		return nil, false
	}
	if !ok {
		return nil, false
	}

	// 代入到 retSet 里
	return []env.FnInFnTTMemItem{ret}, true
}

func (ver *Verifier) paramsSatisfyFnTemplateParamReq(fcFn *ast.FcFn, fnInFnTTMemItem *env.FnInFnTTMemItem) (bool, error) {
	if fnInFnTTMemItem.InFcFn != nil {
		head, ok := fnInFnTTMemItem.InFcFn.FnHead.(*ast.FcFn)
		if !ok {
			return false, nil
		}

		for i, setWhereParamIsIn := range head.Params {
			ok, err := ver.VerFactStmt(ast.NewInFactWithFc(fcFn.Params[i], setWhereParamIsIn), Round0NoMsg)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}

		return true, nil

	} else {
		if len(fcFn.Params) != len(fnInFnTTMemItem.FnTemplateStmt.Params) {
			return false, fmt.Errorf("parameters in %s must be %d, %s in %s is not valid", fcFn.FnHead, len(fnInFnTTMemItem.FnTemplateStmt.Params), fcFn, fcFn)
		}

		for i := range fcFn.Params {
			inFact := ast.NewInFactWithFc(fcFn.Params[i], fnInFnTTMemItem.FnTemplateStmt.ParamSets[i])
			ok, err := ver.VerFactStmt(inFact, Round0NoMsg)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}

		for _, domFact := range fnInFnTTMemItem.FnTemplateStmt.DomFacts {
			ok, err := ver.VerFactStmt(domFact, Round0NoMsg)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}

		return true, nil
	}

}
