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
func (ver *Verifier) checkSpecFactReq_InFact_UseBtRules(stmt *ast.SpecFactStmt) (bool, error) {
	ok := ver.env.AreAtomsInFcAreDeclared(stmt.Params[0], map[string]struct{}{})
	if !ok {
		return false, fmt.Errorf(env.AtomsInFcNotDeclaredMsg(stmt.Params[0]))
	}

	if _, ok := stmt.Params[1].(*ast.FcFn); !ok {
		return false, nil
	}

	head, ok := stmt.Params[1].(*ast.FcFn).IsFcFn_HasAtomHead_ReturnHead()
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
	stateNoMsg := state.toNoMsg()
	for _, param := range stmt.Params {
		ok, err := ver.fcSatisfyFnRequirement(param, stateNoMsg)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, parametersDoNotSatisfyFnReq(param.String(), param.String())
		}
	}

	// 所有的传入的参数符号 prop 的要求 以及 stmt name 确实是个 prop。这貌似不需要检查，因为每次你得到新的事实时候，已经检查过了
	// 但是最好在这里警告一下用户，如果不满足prop的要求的话，可能出问题

	*state = state.toReqOk()
	return true, nil
}

func (ver *Verifier) fcSatisfyFnRequirement(fc ast.Fc, state VerState) (bool, error) {
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
	} else if ast.IsFnFcFn(fcAsFcFn) {
		return true, nil
	} else if ver.isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj(fcAsFcFn) {
		return ver.isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj_CheckRequirement(fcAsFcFn, state)
	} else if ast.IsFcAtomAndEqualToStr(fcAsFcFn.FnHead, glob.KeywordSetDefinedByReplacement) {
		return ver.setDefinedByReplacementFnRequirement(fcAsFcFn, state)
	} else {
		return ver.fcFnSatisfy_FnTemplate_Requirement(fcAsFcFn, state)
	}
}

// func (ver *Verifier) domOfFnRequirement(fc *ast.FcFn) (bool, error) {
// 	if len(fc.Params) != 1 {
// 		return false, fmt.Errorf("parameters in %s must be 1, %s in %s is not valid", fc.FnHead, fc, fc)
// 	}

// 	// param must be a function
// 	_, ok := ver.env.GetFnTemplateOfFc(fc.Params[0])
// 	if !ok {
// 		return false, fmt.Errorf("%s failed: %s must be a function", fc, fc.Params[0])
// 	}

// 	return true, nil
// }

// func isArithmeticFn(fc ast.Fc) bool {
// 	if ok := ast.IsFn_WithHeadNameInSlice(fc, []string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower, glob.KeySymbolPercent}); !ok {
// 		return false
// 	}

// 	return true
// }

// func (ver *Verifier) fcFnSatisfyFnTemplate_FnTemplate_Requirement(fc ast.Fc, state VerState) (bool, error) {
// 	ok, err := ver.fcFnSatisfy_FnTemplate_Requirement(fc, state)
// 	if err != nil {
// 		return false, err
// 	}

// 	return ok, nil
// }

func (ver *Verifier) fcFnSatisfy_FnTemplate_Requirement(fc ast.Fc, state VerState) (bool, error) {
	var err error

	asFcFn, ok := fc.(*ast.FcFn)
	if !ok {
		return false, fmt.Errorf("%s is not a function", fc)
	}

	fnTemplateSlice, ok := ver.env.GetFnTemplateSliceTheFnIsIn(asFcFn.FnHead.String())
	if !ok {
		return false, nil
	}

	for i := len(fnTemplateSlice) - 1; i >= 0; i-- {
		ok, err = ver.fcFnParamsSatisfyFnTemplateNoNameRequirement(asFcFn, fnTemplateSlice[i].FnTemplateStmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}

// TODO: 这里需要检查，setParam是否是自由变量
// func (ver *Verifier) fcFnSatisfy_FnTemplateReq(fc ast.Fc, state VerState) (bool, error) {
// 	asFcFn, ok := fc.(*ast.FcFn)
// 	if !ok {
// 		return false, fmt.Errorf("%s is not a function", fc)
// 	}

// 	templatesOfEachLevel, fcOfEachLevel, ok := ver.env.GetTemplateOfFcFnRecursively(asFcFn)

// 	if !ok {
// 		return false, nil
// 	}

// 	for i := range templatesOfEachLevel {
// 		ok, err := ver.fcFnParamsSatisfyFnTemplateRequirement(fcOfEachLevel[i].Params, templatesOfEachLevel[i], state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if !ok {
// 			return false, nil
// 		}
// 	}

// 	// store the fact that the parameters satisfy the requirement of the function
// 	// REMARK 这里必须要存储，否则很多关于函数的事实是不工作的。但这里牵扯到一个问题是，这里以下释放这么多事实，是不是浪费了。而且我不清楚是只要释放最后一位的性质，还是每一位都要释放
// 	ok, err := ver.env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(fcOfEachLevel[len(fcOfEachLevel)-1], templatesOfEachLevel[len(templatesOfEachLevel)-1])
// 	if err != nil {
// 		return false, err
// 	}

// 	if !ok {
// 		return false, nil
// 	}

// 	return true, nil
// }

// func (ver *Verifier) arithmeticFnRequirement(fc *ast.FcFn, state VerState) (bool, error) {
// 	// parameter必须是实数
// 	for _, param := range fc.Params {
// 		ok, err := ver.paramIs_R_Z_Q_N(param, state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if !ok {
// 			return false, fmt.Errorf("parameters in %s must be in set %s or %s or %s or %s, %s in %s is not valid", fc.FnHead, glob.KeywordReal, glob.KeywordInteger, glob.KeywordRational, glob.KeywordNatural, param, fc)
// 		}
// 	}

// 	if ast.IsFcAtomAndEqualToStr(fc.FnHead, glob.KeySymbolSlash) {
// 		// 分母不是0
// 		ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{fc.Params[1], ast.FcAtom("0")}), state)
// 		if err != nil || !ok {
// 			return ok, fmt.Errorf("parameters in %s must be not equal to 0. %s != 0 is unknown", fc, fc.Params[1])
// 		}
// 		return true, nil
// 	}

// 	if ast.IsFcAtomAndEqualToStr(fc.FnHead, glob.KeySymbolPercent) {
// 		// 分母不是0
// 		ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{fc.Params[1], ast.FcAtom("0")}), state)
// 		if err != nil || !ok {
// 			return ok, fmt.Errorf("second parameter in %s must be not equal to 0. %s != 0 is unknown", fc, fc.Params[1])
// 		}

// 		// 分子分母必须是整数
// 		ok, err = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fc.Params[0], ast.FcAtom(glob.KeywordInteger)}), state)
// 		if err != nil || !ok {
// 			return ok, err
// 		}
// 		ok, err = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fc.Params[1], ast.FcAtom(glob.KeywordInteger)}), state)
// 		if err != nil || !ok {
// 			return ok, err
// 		}
// 		return true, nil
// 	}

// 	return true, nil
// }

// func (ver *Verifier) fcFnParamsSatisfyFnTemplateRequirement(params []ast.Fc, templateOfFn *ast.FnTemplateStmt, state VerState) (bool, error) {
// 	uniMap := map[string]ast.Fc{}
// 	for i, param := range params {
// 		uniMap[templateOfFn.Params[i]] = param
// 	}

// 	paramSets, instantiatedDomFacts, _, _, err := templateOfFn.InstantiateFnTWithoutChangingTName(uniMap)
// 	if err != nil {
// 		return false, err
// 	}

// 	for i, paramSet := range paramSets {
// 		ok, err := ver.VerFactStmt(ast.NewInFactWithFc(params[i], paramSet), state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if !ok {
// 			return false, fmt.Errorf("in fact %s is unknown", ast.NewInFactWithFc(params[i], paramSet))
// 		}
// 	}

// 	for _, domFact := range instantiatedDomFacts {
// 		ok, err := ver.VerFactStmt(domFact, state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if !ok {
// 			return false, fmt.Errorf("dom fact %s is unknown", domFact)
// 		}
// 	}

// 	return true, nil
// }

func (ver *Verifier) fcFnParamsSatisfyFnTemplateNoNameRequirement(fcFn *ast.FcFn, templateOfFn *ast.FnTStruct, state VerState) (bool, error) {
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

// func (ver *Verifier) paramIs_R_Z_Q_N(fc ast.Fc, state VerState) (bool, error) {
// 	inRFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fc, ast.FcAtom(glob.KeywordReal)})
// 	ok, err := ver.VerFactStmt(inRFact, state)
// 	if err != nil {
// 		return false, ver.verErr(err, "failed to check %s", inRFact.String())
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	ok, err = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fc, ast.FcAtom(glob.KeywordInteger)}), state)
// 	if err != nil {
// 		return false, ver.verErr(err, "parameters in %s must be in set %s, %s in %s is not valid", fc, glob.KeywordInteger, fc, fc)
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	ok, err = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fc, ast.FcAtom(glob.KeywordRational)}), state)
// 	if err != nil {
// 		return false, ver.verErr(err, "parameters in %s must be in set %s, %s in %s is not valid", fc, glob.KeywordRational, fc, fc)
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	ok, err = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{fc, ast.FcAtom(glob.KeywordNatural)}), state)
// 	if err != nil {
// 		return false, ver.verErr(err, "parameters in %s must be in set %s, %s in %s is not valid", fc, glob.KeywordNatural, fc, fc)
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	return false, nil
// }

// TODO: 这里需要检查！
func (ver *Verifier) setDefinedByReplacementFnRequirement(fc *ast.FcFn, state VerState) (bool, error) {
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

func (ver *Verifier) isFcFnWithHeadNameBuiltinAndCanTakeInAnyObj_CheckRequirement(fc *ast.FcFn, state VerState) (bool, error) {
	for _, param := range fc.Params {
		ok, err := ver.fcSatisfyFnRequirement(param, state)
		if err != nil || !ok {
			return false, parametersDoNotSatisfyFnReq(param.String(), fc.String())
		}
	}

	return true, nil
}

func (ver *Verifier) lenFnRequirement(fc *ast.FcFn, state VerState) (bool, error) {
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
