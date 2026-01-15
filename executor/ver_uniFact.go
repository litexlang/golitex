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

func (ver *Verifier) verUniFact(oldStmt *ast.UniFactStmt, state *VerState) *glob.VerRet {
	ret := ver.verUniFact_checkFactOneByOne(oldStmt, state)
	if ret.IsTrue() || ret.IsErr() {
		return ret
	}

	// Try using infer if applicable
	return ver.verUniFact_useInfer(oldStmt, state)
}

func (ver *Verifier) verUniFact_checkFactOneByOne(oldStmt *ast.UniFactStmt, state *VerState) *glob.VerRet {
	if state.isFinalRound() {
		return glob.NewEmptyVerRetUnknown()
	}

	// 在局部环境声明新变量
	ver.newEnv()
	defer ver.deleteEnv()

	newStmtPtr, err := ver.PreprocessUniFactParams_DeclareParams(oldStmt)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, oldStmt.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	// 检查所有 paramSet 是否都是 list_set，如果是，自动使用 enum 的逻辑
	if ver.allParamSetsAreListSet(newStmtPtr.ParamSets) {
		verRet := ver.verUniFactByProveByEnum(newStmtPtr, state)
		if verRet.IsTrue() || verRet.IsErr() {
			return verRet
		}
		// 如果 enum 失败，继续使用常规验证方法
	}

	// know cond facts
	for _, condFact := range newStmtPtr.DomFacts {
		ret := ver.Env.NewFactWithCheckingNameDefined(condFact)
		if ret.IsErr() {
			return glob.NewVerMsg(glob.StmtRetTypeError, condFact.String(), glob.BuiltinLine0, []string{ret.String()})
		}
	}

	return ver.uniFact_checkThenFacts(newStmtPtr, state)
}

func (ver *Verifier) verUniFact_useInfer(oldStmt *ast.UniFactStmt, state *VerState) *glob.VerRet {
	if state.isFinalRound() {
		return glob.NewEmptyVerRetUnknown()
	}

	// 0. 如果dom和then里全是or_spec 那可以继续，否则就不行
	domFactsReversible := []ast.Spec_OrFact{}
	for _, domFact := range oldStmt.DomFacts {
		if specFact, ok := domFact.(*ast.SpecFactStmt); ok {
			domFactsReversible = append(domFactsReversible, specFact)
		} else if orStmt, ok := domFact.(*ast.OrStmt); ok {
			domFactsReversible = append(domFactsReversible, orStmt)
		} else {
			// Not all facts are Spec_OrFact, cannot use infer
			return glob.NewEmptyVerRetUnknown()
		}
	}

	thenFactsReversible := []ast.Spec_OrFact{}
	for _, thenFact := range oldStmt.ThenFacts {
		if specFact, ok := thenFact.(*ast.SpecFactStmt); ok {
			thenFactsReversible = append(thenFactsReversible, specFact)
		} else if orStmt, ok := thenFact.(*ast.OrStmt); ok {
			thenFactsReversible = append(thenFactsReversible, orStmt)
		} else {
			// Not all facts are Spec_OrFact, cannot use infer
			return glob.NewEmptyVerRetUnknown()
		}
	}

	ver.newEnv()
	defer ver.deleteEnv()

	// 1. 如果param和当前的环境里冲突了，那就替换成 random
	paramMap, paramMapStrToStr := processUniFactParamsDuplicateDeclared(ver.Env, oldStmt.Params)
	if len(paramMap) > 0 {
		// Replace parameters in UniFactStmt
		newStmtPtr, _, err := useRandomParamToReplaceOriginalParamInUniFact(oldStmt, paramMap, paramMapStrToStr)
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, oldStmt.String(), glob.BuiltinLine0, []string{err.Error()})
		}
		oldStmt = newStmtPtr
		// Rebuild reversible facts with replaced parameters
		domFactsReversible = []ast.Spec_OrFact{}
		for _, domFact := range oldStmt.DomFacts {
			if specFact, ok := domFact.(*ast.SpecFactStmt); ok {
				domFactsReversible = append(domFactsReversible, specFact)
			} else if orStmt, ok := domFact.(*ast.OrStmt); ok {
				domFactsReversible = append(domFactsReversible, orStmt)
			}
		}
		thenFactsReversible = []ast.Spec_OrFact{}
		for _, thenFact := range oldStmt.ThenFacts {
			if specFact, ok := thenFact.(*ast.SpecFactStmt); ok {
				thenFactsReversible = append(thenFactsReversible, specFact)
			} else if orStmt, ok := thenFact.(*ast.OrStmt); ok {
				thenFactsReversible = append(thenFactsReversible, orStmt)
			}
		}
	}

	// 声明param
	defLeftStmt := ast.NewDefLetStmt(oldStmt.Params, oldStmt.ParamSets, oldStmt.DomFacts, oldStmt.Line)
	ret := ver.Env.DefLetStmt(defLeftStmt)
	if ret.IsErr() {
		return glob.NewVerMsg(glob.StmtRetTypeError, oldStmt.String(), glob.BuiltinLine0, []string{ret.String()})
	}

	// 2. 把uni变成 inferStmt，然后执行inferStmt
	inferStmt := ast.NewImplyStmt(domFactsReversible, thenFactsReversible, oldStmt.Line)
	exec := NewExecutor(ver.Env)
	execRet := exec.inferStmt(inferStmt)

	if execRet.IsErr() {
		return glob.NewVerMsg(glob.StmtRetTypeError, oldStmt.String(), glob.BuiltinLine0, []string{execRet.String()})
	} else if execRet.IsTrue() {
		return glob.NewVerMsg(glob.StmtRetTypeTrue, oldStmt.String(), glob.BuiltinLine0, []string{})
	} else {
		return glob.NewEmptyVerRetUnknown()
	}
}

func (ver *Verifier) uniFact_checkThenFacts(stmt *ast.UniFactStmt, state *VerState) *glob.VerRet {
	msgs := []string{}

	// check then facts
	for _, thenFact := range stmt.ThenFacts {
		verRet := ver.VerFactStmt(thenFact, state) // 这个地方有点tricky，这里是可能读入state是any的，而且我要允许读入any
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			if state.WithMsg {
				msgs := append(verRet.VerifyMsgs, fmt.Sprintf("%s is unknown", thenFact))
				return glob.NewVerMsg(glob.StmtRetTypeUnknown, thenFact.String(), glob.BuiltinLine0, msgs)
			}
			return glob.NewEmptyVerRetUnknown()
		}

		// if true, store it
		ret := ver.Env.NewFactWithCheckingNameDefined(thenFact)
		if ret.IsErr() {
			return glob.NewVerMsg(glob.StmtRetTypeError, thenFact.String(), glob.BuiltinLine0, []string{ret.String()})
		}

		msgs = append(msgs, verRet.String())
	}

	if state.WithMsg {
		return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, msgs)
	}
	return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, msgs)
}

func (ver *Verifier) PreprocessUniFactParams_DeclareParams(oldStmt *ast.UniFactStmt) (*ast.UniFactStmt, error) {
	newStmtPtr, _, err := ver.instantiateUniFactWithoutDuplicate(oldStmt)
	if err != nil {
		return nil, err
	}

	// declare
	stmtForDef := ast.NewDefLetStmt(newStmtPtr.Params, newStmtPtr.ParamSets, []ast.FactStmt{}, oldStmt.Line)
	ret := ver.Env.DefLetStmt(stmtForDef)
	if ret.IsErr() {
		return nil, fmt.Errorf(ret.String())
	}

	// 查看param set 是否已经声明
	for _, paramSet := range newStmtPtr.ParamSets {
		ret := ver.Env.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(paramSet, map[string]struct{}{})
		if ret.IsErr() {
			return nil, fmt.Errorf(ret.String())
		}
	}

	return newStmtPtr, nil
}

// allParamSetsAreListSet 检查所有的 paramSet 是否都是 list_set
func (ver *Verifier) allParamSetsAreListSet(paramSets []ast.Obj) bool {
	for _, paramSet := range paramSets {
		// paramSet 是 fnObj 且 头名是 list_set
		// fnObj, ok := paramSet.(*ast.FnObj)
		// if !ok {
		// 	return false
		// }
		// if fnObj.FnHead.String() != glob.KeywordListSet {
		// 	return false
		// }
		// return true

		enumSet := ver.Env.GetListSetEqualToObj(paramSet)
		if enumSet == nil {
			return false
		}

	}
	return true
}

// verUniFactByProveByEnum 使用 enum 的逻辑来验证 forall 语句
func (ver *Verifier) verUniFactByProveByEnum(stmt *ast.UniFactStmt, state *VerState) *glob.VerRet {
	// 获取所有 paramSet 对应的 list_set
	enums := [][]ast.Obj{}
	for _, paramSet := range stmt.ParamSets {
		enumSet := ver.Env.GetListSetEqualToObj(paramSet)
		if enumSet == nil {
			return glob.NewEmptyVerRetUnknown()
		}
		listSetFnObj, ok := enumSet.(*ast.FnObj)
		if !ok {
			return glob.NewEmptyVerRetUnknown()
		}
		enums = append(enums, listSetFnObj.Params)
	}

	// 计算笛卡尔积
	cartesianProductOfObjs := glob.CartesianProduct(enums)

	verifyProcessMsgs := []*glob.VerRet{}

	// 遍历所有组合
	for _, objSlice := range cartesianProductOfObjs {
		uniMap := map[string]ast.Obj{}
		for i, param := range stmt.Params {
			uniMap[param] = objSlice[i]
		}

		// 检查 dom facts
		hasFalseDomFact := false
		for _, domFact := range stmt.DomFacts {
			instantiatedDomFact, err := domFact.InstantiateFact(uniMap)
			if err != nil {
				return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{err.Error()})
			}

			verRet := ver.VerFactStmt(instantiatedDomFact, state)
			if verRet.IsErr() {
				return verRet
			}
			verifyProcessMsgs = append(verifyProcessMsgs, verRet)
			if verRet.IsUnknown() {
				// 如果 dom fact 是 unknown，尝试反转验证
				domFactAs := instantiatedDomFact.(ast.Spec_OrFact)
				for _, fact := range domFactAs.ReverseIsTrue() {
					verRet := ver.VerFactStmt(fact, state)
					if verRet.IsErr() {
						return verRet
					}
					if verRet.IsUnknown() {
						return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("domain fact in universal fact must be true or false, cannot be unknown: %s", instantiatedDomFact)})
					}
					verifyProcessMsgs = append(verifyProcessMsgs, verRet)
				}
				hasFalseDomFact = true
				break
			}
		}

		// 如果 dom fact 为 false，跳过这个组合
		if hasFalseDomFact {
			continue
		}

		// 验证 then facts
		for _, thenFact := range stmt.ThenFacts {
			instantiatedThenFact, err := thenFact.InstantiateFact(uniMap)
			if err != nil {
				return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{err.Error()})
			}

			verRet := ver.VerFactStmt(instantiatedThenFact, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsUnknown() {
				return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("failed to prove instantiated then fact: %s", instantiatedThenFact)})
			}
			verifyProcessMsgs = append(verifyProcessMsgs, verRet)
		}
	}

	// 所有组合都验证通过
	if state.WithMsg {
		msgs := []string{"proved by enumeration (all paramSets are list_set)"}
		return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, msgs)
	}
	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verUniFactWithIff(stmt *ast.UniFactWithIffStmt, state *VerState) *glob.VerRet {
	thenToIff := stmt.NewUniFactWithThenToIff()
	verRet := ver.verUniFact(thenToIff, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	iffToThen := stmt.NewUniFactWithIffToThen()
	verRet = ver.verUniFact(iffToThen, state)
	return verRet
}
