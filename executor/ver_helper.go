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
	glob "golitex/glob"
)

// maybeAddSuccessMsgString is a backward compatibility function for string-based
func (ver *Verifier) maybeAddSuccessMsgString(state *VerState, stmtStr, verifiedByStr string, execRet *glob.VerRet) *glob.VerRet {
	if state == nil {
		panic("")
	}

	if state.WithMsg {
		execRet.VerifyMsgs = append(execRet.VerifyMsgs, successVerStringString(stmtStr, verifiedByStr).VerifyMsgs...)
		return execRet
	}
	return execRet
}

// maybeAddSuccessMsgVerMsg adds a VerMsg to execRet if state.WithMsg is true

func IsTrueOrErr(ok bool, err error) bool {
	return ok || err != nil
}

func IsFalseOrErr(ok bool, err error) bool {
	return !ok || err != nil
}

// func ObjIsNotSet(obj ast.Obj) bool {
// 	return !ast.ObjIsKeywordSet(obj)
// }

// ordinalSuffix converts a number to its ordinal form (1st, 2nd, 3rd, 4th, etc.)
func ordinalSuffix(n int) string {
	if n < 0 {
		return fmt.Sprintf("%dth", n)
	}

	// Special cases for 11, 12, 13 which all use "th"
	if n%100 >= 11 && n%100 <= 13 {
		return fmt.Sprintf("%dth", n)
	}

	// Regular cases based on last digit
	switch n % 10 {
	case 1:
		return fmt.Sprintf("%dst", n)
	case 2:
		return fmt.Sprintf("%dnd", n)
	case 3:
		return fmt.Sprintf("%drd", n)
	default:
		return fmt.Sprintf("%dth", n)
	}
}

func (ver *Verifier) replaceExistParamsWithRandomNames(existStruct *ast.ExistStFactStruct) *ast.ExistStFactStruct {
	if len(existStruct.ExistFreeParams) == 0 {
		return existStruct
	}

	// 生成随机名称替换映射
	paramReplaceMap := map[string]ast.Obj{}
	newExistParams := make([]string, len(existStruct.ExistFreeParams))
	usedNames := map[string]struct{}{}

	for i, oldParam := range existStruct.ExistFreeParams {
		// 生成一个不冲突的随机名称
		newParamName := ver.Env.GenerateUndeclaredRandomName_AndNotInMap(usedNames)
		newExistParams[i] = newParamName
		usedNames[newParamName] = struct{}{}
		paramReplaceMap[oldParam] = ast.Atom(newParamName)
	}

	// 替换 ExistFreeParamSets 中的参数引用
	newExistParamSets := make([]ast.Obj, len(existStruct.ExistFreeParamSets))
	for i, paramSet := range existStruct.ExistFreeParamSets {
		newParamSet := paramSet
		for oldParam, newParam := range paramReplaceMap {
			newParamSet = newParamSet.ReplaceObj(ast.Atom(oldParam), newParam)
		}
		newExistParamSets[i] = newParamSet
	}

	// 替换 Params 中的参数引用
	newParams := make([]ast.Obj, len(existStruct.Params))
	for i, param := range existStruct.Params {
		newParam := param
		for oldParam, newParamObj := range paramReplaceMap {
			newParam = newParam.ReplaceObj(ast.Atom(oldParam), newParamObj)
		}
		newParams[i] = newParam
	}

	return ast.NewExistStFactStruct(existStruct.FactType, existStruct.PropName, existStruct.IsPropTrue, newExistParams, newExistParamSets, newParams, existStruct.Line)
}
