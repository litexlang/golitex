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
	env "golitex/environment"
	glob "golitex/glob"
)

// 如果我尝试通过逐个子命题 m 的方式，使用“其余为假，m 为真”的方法去验证 a ∨ b ∨ c ∨ ... ∨ n，但全部尝试都失败了，那就可以断言 a ∨ b ∨ c ∨ ... ∨ n 为假。反过来，只要有一次成立了，那就可以断言 a ∨ b ∨ c ∨ ... ∨ n 为真。

// 反过来，用已知的 a ∨ b ∨ c ∨ ... ∨ n 为真，去验证 a ，需要先验证b, c, ... , n 为假，才能得到 a 为真。

// func (ver *Verifier) verOrStmt(stmt *ast.OrStmt, state *VerState) *glob.VerRet {
// nextState := state.GetAddRound()
// for i := range stmt.Facts {
// 	verRet := ver.verFactAtIndex_WhenOthersAreFalse(stmt.Facts, i, nextState)
// 	if verRet.IsErr() {
// 		return verRet
// 	}
// 	if verRet.IsTrue() {
// 		if state.WithMsg {
// 			msg := fmt.Sprintf("%s is true when all others facts in the or statement are false", stmt.Facts[i])
// 			return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, append([]string{msg}, verRet.VerifyMsgs...))
// 		}
// 		return glob.NewEmptyVerRetTrue()
// 	}
// }
// return glob.NewEmptyVerRetUnknown()
// }

// func (ver *Verifier) verFactAtIndex_WhenOthersAreFalse(facts []ast.SpecificFactStmt, i int, state *VerState) *glob.VerRet {
// 	ver.newEnv()
// 	defer ver.deleteEnv()

// 	for j := range facts {
// 		if j == i {
// 			continue
// 		}
// 		ret := ver.Env.NewFactWithCheckingNameDefined(facts[j].ReverseIsTrue()[0])
// 		if ret.IsErr() {
// 			return glob.NewVerMsg(glob.StmtRetTypeError, facts[j].String(), glob.BuiltinLine0, []string{ret.String()})
// 		}
// 	}

// 	verRet := ver.VerFactStmt(facts[i], state)
// 	return verRet
// }

func (ver *Verifier) verOrStmt(stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	ret := ver.verOrStmt_UseOrMem(stmt, state)
	if ret.IsTrue() || ret.IsErr() {
		return ret
	}

	ret = ver.verOrStmt_UseOrInUniFactMem(stmt, state)
	if ret.IsTrue() || ret.IsErr() {
		return ret
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
		return glob.NewEmptyVerRetUnknown()
	}

	// 检查每个 key 对应的 value 长度是否相同
	for key, givenValues := range givenSpecFactWithTheSameNameMap {
		knownValues, exists := knownSpecFactWithTheSameNameMap[key]
		if !exists {
			return glob.NewEmptyVerRetUnknown()
		}
		if len(givenValues) != len(knownValues) {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	for key := range givenSpecFactWithTheSameNameMap {
		verified := false

		knownFacts := knownSpecFactWithTheSameNameMap[key]
		givenFacts := givenSpecFactWithTheSameNameMap[key]

		// 生成 givenFacts 的所有排列
		permutations := generatePermutations(givenFacts)
		fmt.Printf("Key '%s': Generated %d permutations for %d facts\n", key, len(permutations), len(givenFacts))
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

func (ver *Verifier) matchSpecFactWhenCheckOr(knowns []ast.SpecificFactStmt, givens []ast.SpecificFactStmt, state *VerState) *glob.VerRet {
	for i := range knowns {
		known := knowns[i]
		given := givens[i]

		if known.GetFactType() != given.GetFactType() {
			return glob.NewEmptyVerRetUnknown()
		}

		if known.String() != given.String() {
			return glob.NewEmptyVerRetUnknown()
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
