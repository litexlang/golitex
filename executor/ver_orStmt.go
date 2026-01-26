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
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) verOrStmt(stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	for i := range len(stmt.Facts) {
		ret := ver.verOrStmtByAssumeAllFactsAreFalseToProveTheRemainingOneIsTrue(stmt, i, state)
		if ret.IsTrue() || ret.IsErr() {
			return ret
		}
	}

	ret := ver.verOrStmt_UseOrMem(stmt, state)
	if ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if !state.isFinalRound() {
		ret = ver.verOrStmt_UseOrInUniFactMem(stmt, state)
		if ret.IsTrue() || ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verOrStmt_UseOrMem(stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.orFact_UseOrMem_atCurEnv(curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.orFact_UseOrMem_atCurEnv(curEnv, stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.orFact_UseOrMem_atCurEnv(&curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) orFact_UseOrMem_atCurEnv(curEnv *env.EnvMemory, stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	knownOrFacts, got := curEnv.OrFactsMem[string(stmt.Facts[0].GetPropName())]
	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	for _, knownOrFact := range knownOrFacts {
		ret := ver.useKnownOrFactToCheckGivenOrFact(stmt, knownOrFact, state)
		if ret.IsTrue() || ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) useKnownOrFactToCheckGivenOrFact(given *ast.OrStmt, known *ast.OrStmt, state *VerState) *glob.VerRet {
	givenSpecFactWithTheSameNameMap, knownSpecFactWithTheSameNameMap, isValid := ver.groupFactsByPropNameAndValidate(given, known)
	if !isValid {
		return glob.NewEmptyVerRetUnknown()
	}

	for key := range givenSpecFactWithTheSameNameMap {
		verified := false

		knownFacts := knownSpecFactWithTheSameNameMap[key]
		givenFacts := givenSpecFactWithTheSameNameMap[key]

		// 生成 givenFacts 的所有排列
		permutations := generatePermutations(givenFacts)
		for _, perm := range permutations {
			ret := ver.matchSpecFactWhenCheckOr(knownFacts, perm, state)
			if ret.IsTrue() {
				verified = true
				break
			}
		}

		if !verified {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	return glob.NewEmptyVerRetTrue()
}

// groupFactsByPropNameAndValidate 将 given 和 known 的 facts 按 propName 分组，并验证两个 map 的结构是否匹配
// 返回 given 的 map、known 的 map 和是否有效的标志
func (ver *Verifier) groupFactsByPropNameAndValidate(given *ast.OrStmt, known *ast.OrStmt) (map[string][]ast.SpecificFactStmt, map[string][]ast.SpecificFactStmt, bool) {
	givenSpecFactWithTheSameNameMap := map[string][]ast.SpecificFactStmt{}
	knownSpecFactWithTheSameNameMap := map[string][]ast.SpecificFactStmt{}

	for _, fact := range given.Facts {
		propName := string(fact.GetPropName())
		if _, got := givenSpecFactWithTheSameNameMap[propName]; got {
			givenSpecFactWithTheSameNameMap[propName] = append(givenSpecFactWithTheSameNameMap[propName], fact)
		} else {
			givenSpecFactWithTheSameNameMap[propName] = []ast.SpecificFactStmt{fact}
		}
	}

	for _, fact := range known.Facts {
		propName := string(fact.GetPropName())
		if _, got := knownSpecFactWithTheSameNameMap[propName]; got {
			knownSpecFactWithTheSameNameMap[propName] = append(knownSpecFactWithTheSameNameMap[propName], fact)
		} else {
			knownSpecFactWithTheSameNameMap[propName] = []ast.SpecificFactStmt{fact}
		}
	}

	// 检查两个 map 的 key 数量是否相同
	if len(givenSpecFactWithTheSameNameMap) != len(knownSpecFactWithTheSameNameMap) {
		return givenSpecFactWithTheSameNameMap, knownSpecFactWithTheSameNameMap, false
	}

	// 检查每个 key 对应的 value 长度是否相同
	for key, givenValues := range givenSpecFactWithTheSameNameMap {
		knownValues, exists := knownSpecFactWithTheSameNameMap[key]
		if !exists {
			return givenSpecFactWithTheSameNameMap, knownSpecFactWithTheSameNameMap, false
		}
		if len(givenValues) != len(knownValues) {
			return givenSpecFactWithTheSameNameMap, knownSpecFactWithTheSameNameMap, false
		}
	}

	return givenSpecFactWithTheSameNameMap, knownSpecFactWithTheSameNameMap, true
}

func (ver *Verifier) matchSpecFactWhenCheckOr(knowns []ast.SpecificFactStmt, givens []ast.SpecificFactStmt, state *VerState) *glob.VerRet {
	for i := range knowns {
		known := knowns[i]
		given := givens[i]

		if known.GetFactType() != given.GetFactType() {
			return glob.NewEmptyVerRetUnknown()
		}

		switch knownAs := known.(type) {
		case *ast.PureSpecificFactStmt:
			if len(knownAs.Params) != len(given.(*ast.PureSpecificFactStmt).Params) {
				return glob.NewEmptyVerRetUnknown()
			}

			for param := range knownAs.Params {
				ret := ver.VerFactStmt(ast.NewEqualFact(knownAs.Params[param], given.(*ast.PureSpecificFactStmt).Params[param]), state)
				if ret.IsNotTrue() {
					return glob.NewEmptyVerRetUnknown()
				}
			}

		case *ast.ExistSpecificFactStmt:
			if knownAs.String() != given.String() {
				return glob.NewEmptyVerRetUnknown()
			}
		}

	}

	return glob.NewEmptyVerRetTrue()
}

// generatePermutations 生成给定切片的所有排列
func generatePermutations(facts []ast.SpecificFactStmt) [][]ast.SpecificFactStmt {
	if len(facts) == 0 {
		return [][]ast.SpecificFactStmt{{}}
	}
	if len(facts) == 1 {
		return [][]ast.SpecificFactStmt{facts}
	}

	var result [][]ast.SpecificFactStmt
	for i := range facts {
		// 创建不包含当前元素的切片
		remaining := make([]ast.SpecificFactStmt, 0, len(facts)-1)
		remaining = append(remaining, facts[:i]...)
		remaining = append(remaining, facts[i+1:]...)

		// 递归生成剩余元素的排列
		subPermutations := generatePermutations(remaining)

		// 将当前元素添加到每个子排列的开头
		for _, perm := range subPermutations {
			newPerm := make([]ast.SpecificFactStmt, 0, len(facts))
			newPerm = append(newPerm, facts[i])
			newPerm = append(newPerm, perm...)
			result = append(result, newPerm)
		}
	}

	return result
}

func (ver *Verifier) verOrStmtByAssumeAllFactsAreFalseToProveTheRemainingOneIsTrue(stmt *ast.OrStmt, index int, state *VerState) *glob.VerRet {
	ver.newEnv()
	defer ver.deleteEnv()

	for i := range len(stmt.Facts) {
		if i == index {
			continue
		}
		ret := ver.Env.NewFactWithCheckingNameDefined(stmt.Facts[i])
		if ret.IsNotTrue() {
			return glob.NewEmptyVerRetUnknown().AddUnknown(ret.String())
		}
	}

	ret := ver.VerFactStmt(stmt.Facts[index], state)
	if ret.IsNotTrue() {
		return glob.NewEmptyVerRetUnknown().AddUnknown(ret.String())
	}

	return glob.NewEmptyVerRetTrue()
}
