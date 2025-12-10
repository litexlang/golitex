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
// Litex Zulip community: https://litexlang.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// verifySpecFactFnRequirement 验证 SpecFactStmt 中所有对象都符合函数要求
func (ver *Verifier) verifySpecFactFnRequirement(fact *ast.SpecFactStmt, state *VerState) ExecRet {
	stateNoMsg := state.GetNoMsg()

	// 验证所有参数
	for _, paramObj := range fact.Params {
		verRet := ver.objIsDefinedAtomOrIsFnSatisfyItsReq(paramObj, stateNoMsg)
		if verRet.IsErr() {
			return NewExecErr(fmt.Sprintf("parameter %s in fact %s does not satisfy function requirement: %s", paramObj, fact, verRet.String()))
		}
		if verRet.IsUnknown() {
			return NewExecErr(fmt.Sprintf("parameter %s in fact %s does not satisfy function requirement: %s", paramObj, fact, verRet.String()))
		}
	}

	return NewEmptyExecTrue()
}

// verifyOrFactFnRequirement 验证 OrStmt 中所有对象都符合函数要求
func (ver *Verifier) verifyOrFactFnRequirement(fact *ast.OrStmt, state *VerState) ExecRet {
	// 验证每个 or fact 中的 spec fact
	for _, specFact := range fact.Facts {
		verRet := ver.verifySpecFactFnRequirement(specFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	return NewEmptyExecTrue()
}

// verifyFactFnRequirement 验证任意类型的 fact 中所有对象都符合函数要求
func (ver *Verifier) verifyFactFnRequirement(fact ast.FactStmt, state *VerState) ExecRet {
	switch asFact := fact.(type) {
	case *ast.SpecFactStmt:
		return ver.verifySpecFactFnRequirement(asFact, state)
	case *ast.OrStmt:
		return ver.verifyOrFactFnRequirement(asFact, state)
	case *ast.UniFactStmt:
		return ver.verifyUniFactFnRequirement(asFact, state)
	case *ast.UniFactWithIffStmt:
		return ver.verifyUniFactWithIffFnRequirement(asFact, state)
	case *ast.EqualsFactStmt:
		return ver.verifyEqualsFactFnRequirement(asFact, state)
	default:
		return NewExecErr(fmt.Sprintf("unexpected fact type: %T", asFact))
	}
}

func (ver *Verifier) verifyEqualsFactFnRequirement(equalsFact *ast.EqualsFactStmt, state *VerState) ExecRet {
	for _, fact := range equalsFact.ToEqualFacts() {
		verRet := ver.verifyFactFnRequirement(fact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	return NewEmptyExecTrue()
}

// verifyAndDeclareParamsIteratively 逐步迭代验证和声明参数
// 对于每个参数 i：
// 1. 验证第i个set是OK的
// 2. 声明第i个obj
// 3. 继续迭代下一个
func (ver *Verifier) verifyAndDeclareParamsIteratively(params []string, paramSets []ast.Obj, state *VerState) (map[string]ast.Obj, ExecRet) {
	if len(params) != len(paramSets) {
		return nil, NewExecErr(fmt.Sprintf("number of params (%d) and param sets (%d) must be equal", len(params), len(paramSets)))
	}

	paramMap := make(map[string]ast.Obj)
	stateNoMsg := state.GetNoMsg()

	// 逐步迭代每个参数
	for i := range params {
		param := params[i]
		paramSet := paramSets[i]

		// 1. 验证第i个set是OK的（需要先实例化paramSet，因为可能依赖前面已声明的参数）
		var instantiatedParamSet ast.Obj
		if len(paramMap) > 0 {
			inst, err := paramSet.Instantiate(paramMap)
			if err != nil {
				return nil, NewExecErr(fmt.Sprintf("failed to instantiate param set %s for param %s: %s", paramSet, param, err))
			}
			instantiatedParamSet = inst
		} else {
			instantiatedParamSet = paramSet
		}

		// 验证 paramSet 是否满足函数要求
		verRet := ver.objIsDefinedAtomOrIsFnSatisfyItsReq(instantiatedParamSet, stateNoMsg)
		if verRet.IsErr() {
			return nil, NewExecErr(fmt.Sprintf("param set %s for param %s does not satisfy function requirement: %s", instantiatedParamSet, param, verRet.String()))
		}
		if verRet.IsUnknown() {
			return nil, NewExecErr(fmt.Sprintf("param set %s for param %s does not satisfy function requirement: %s", instantiatedParamSet, param, verRet.String()))
		}

		// 2. 检查 param 是否已在母环境声明过，如果是则生成随机名称
		paramAtom := ast.Atom(param)
		ret := ver.Env.IsAtomDeclared(paramAtom, map[string]struct{}{})
		var actualParamName string
		if ret.IsTrue() {
			// param 已声明，生成随机名称
			actualParamName = ver.Env.GenerateUndeclaredRandomName()
			paramMap[param] = ast.Atom(actualParamName)
		} else {
			// param 未声明，直接使用
			actualParamName = param
			paramMap[param] = ast.Atom(param)
		}

		// 3. 声明第i个obj（使用实例化后的paramSet）
		defObjStmt := ast.NewDefLetStmt(
			[]string{actualParamName},
			[]ast.Obj{instantiatedParamSet},
			[]ast.FactStmt{},
			glob.BuiltinLine,
		)
		ret = ver.Env.DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(defObjStmt)
		if ret.IsErr() {
			return nil, NewExecErr(fmt.Sprintf("failed to declare parameter %s: %s", actualParamName, ret.String()))
		}
	}

	return paramMap, NewEmptyExecTrue()
}

// verifyUniFactFnRequirement 验证 UniFactStmt 中所有对象都符合函数要求
// 新开环境，如果 param 已经声明过了，那就换一个名字，然后实例化整个 fact
func (ver *Verifier) verifyUniFactFnRequirement(uniFact *ast.UniFactStmt, state *VerState) ExecRet {
	// 保存当前环境
	parentEnv := ver.Env

	// 创建新环境
	ver.newEnv(parentEnv)
	defer func() {
		ver.Env = parentEnv
	}()

	// 逐步迭代验证和声明参数
	paramMap, verRet := ver.verifyAndDeclareParamsIteratively(uniFact.Params, uniFact.ParamSets, state)
	if verRet.IsErr() {
		return verRet
	}

	// 如果有参数需要重命名，实例化整个 fact
	var instantiatedUniFact *ast.UniFactStmt
	if len(paramMap) > 0 {
		// 检查是否有参数被重命名
		hasRename := false
		for origParam, newParamObj := range paramMap {
			if string(newParamObj.(ast.Atom)) != origParam {
				hasRename = true
				break
			}
		}
		if hasRename {
			instFact, err := uniFact.InstantiateFact(paramMap)
			if err != nil {
				return NewExecErr(fmt.Sprintf("failed to instantiate uni fact %s: %s", uniFact, err))
			}
			var ok bool
			instantiatedUniFact, ok = instFact.(*ast.UniFactStmt)
			if !ok {
				return NewExecErr(fmt.Sprintf("instantiated fact is not UniFactStmt: %T", instFact))
			}
		} else {
			instantiatedUniFact = uniFact
		}
	} else {
		instantiatedUniFact = uniFact
	}

	// 验证 DomFacts 中的所有对象
	for _, domFact := range instantiatedUniFact.DomFacts {
		verRet := ver.verifyFactFnRequirement(domFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	// 验证 ThenFacts 中的所有对象
	for _, thenFact := range instantiatedUniFact.ThenFacts {
		verRet := ver.verifyFactFnRequirement(thenFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	return NewEmptyExecTrue()
}

// verifyUniFactWithIffFnRequirement 验证 UniFactWithIffStmt 中所有对象都符合函数要求
func (ver *Verifier) verifyUniFactWithIffFnRequirement(uniFactWithIff *ast.UniFactWithIffStmt, state *VerState) ExecRet {
	// 先验证 UniFact 部分
	verRet := ver.verifyUniFactFnRequirement(uniFactWithIff.UniFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return verRet
	}

	// 验证 IffFacts 中的所有对象
	for _, iffFact := range uniFactWithIff.IffFacts {
		verRet := ver.verifyFactFnRequirement(iffFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	return NewEmptyExecTrue()
}

// verifyIntensionalSetFactsFnRequirement 验证 intensional set 中所有事实都符合函数要求
// 1. 如果当前的param，即第一个参数，已经在母环境声明过了，那就随机生成一个环境里没有的名字，然后把所有的fact里的这个param inst成新的随机名
// 2. 然后随机名（或者这个param）声名成这个母集，即obj.Params[1]的元素
// 3. 然后验证所有事实里出现的obj都是符合fnReq的
// func (ver *Verifier) verifyIntensionalSetFactsFnRequirement(objAsFnObj *ast.FnObj, state *VerState) ExecRet {
// 	// 从 intensional set 对象中提取 param, parentSet, facts
// 	param, parentSet, facts, err := ast.GetParamParentSetFactsFromIntensionalSetObj(objAsFnObj)
// 	if err != nil {
// 		return NewExecErr(fmt.Sprintf("failed to extract intensional set information: %s", err))
// 	}

// 	// 保存当前环境
// 	parentEnv := ver.Env

// 	// 创建新环境
// 	ver.newEnv(parentEnv)
// 	defer func() {
// 		ver.Env = parentEnv
// 	}()

// 	// 1. 检查 param 是否已在母环境声明过
// 	paramAtom := ast.Atom(param)
// 	ret := parentEnv.IsAtomDeclared(paramAtom, map[string]struct{}{})
// 	var actualParamName string

// 	if ret.IsTrue() {
// 		// param 已声明，生成随机名称
// 		actualParamName = parentEnv.GenerateUndeclaredRandomName()
// 		uniMap := map[string]ast.Obj{
// 			param: ast.Atom(actualParamName),
// 		}

// 		// 实例化所有 facts
// 		instantiatedFacts := []ast.FactStmt{}
// 		for _, fact := range facts {
// 			instFact, err := fact.InstantiateFact(uniMap)
// 			if err != nil {
// 				return NewExecErr(fmt.Sprintf("failed to instantiate fact %s: %s", fact, err))
// 			}
// 			instantiatedFacts = append(instantiatedFacts, instFact)
// 		}
// 		facts = instantiatedFacts
// 	} else {
// 		// param 未声明，直接使用
// 		actualParamName = param
// 	}

// 	// 2. 声明 param（或随机名）为 parentSet 的元素
// 	paramObj := ast.Atom(actualParamName)
// 	defObjStmt := ast.NewDefLetStmt(
// 		[]string{actualParamName},
// 		[]ast.Obj{parentSet},
// 		[]ast.FactStmt{ast.NewInFactWithObj(paramObj, parentSet)},
// 		glob.BuiltinLine,
// 	)
// 	ret = ver.Env.DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(defObjStmt)
// 	if ret.IsErr() {
// 		return NewExecErr(fmt.Sprintf("failed to declare parameter %s in parent set: %s", actualParamName, ret.String()))
// 	}

// 	// 3. 验证所有事实里出现的 obj 都是符合 fnReq 的
// 	for _, fact := range facts {
// 		verRet := ver.verifyFactFnRequirement(fact, state)
// 		if verRet.IsErr() {
// 			return verRet
// 		}
// 		if verRet.IsUnknown() {
// 			return verRet
// 		}
// 	}

// 	return NewEmptyExecTrue()
// }
