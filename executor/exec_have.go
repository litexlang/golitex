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

func (exec *Executor) haveObjEqualStmt(stmt *ast.HaveObjEqualStmt) ast.StmtRet {
	ver := NewVerifier(exec.Env)

	newFactMsgs := []string{}
	defineMsgs := []string{}
	verifyProcessMsgs := []ast.VerRet{}

	for i := range len(stmt.ObjNames) {
		objName := stmt.ObjNames[i]
		objEqualTo := stmt.ObjEqualTos[i]
		objSet := stmt.ObjSets[i]

		// 验证等号右边的对象是否已定义
		if ret := ver.objIsDefinedAtomOrIsFnSatisfyItsReq(objEqualTo, Round0NoMsg()); ret.IsNotTrue() {
			return ret.ToStmtRet()
		}

		// 验证等号右边的对象是否在指定的集合中
		inFact := ast.NewInFactWithObj(objEqualTo, objSet)
		verRet := ver.VerFactStmt(inFact, Round0Msg())
		if verRet.IsErr() {
			return ast.StmtErrRet(stmt, verRet.String())
		}
		if verRet.IsUnknown() {
			return ast.StmtErrRet(stmt, fmt.Sprintf("%s is not in %s", objName, objSet))
		}
		verifyProcessMsgs = append(verifyProcessMsgs, verRet)

		// 检查等号右边的对象中的名称是否存在
		ret := exec.Env.LookupNamesInObj(objEqualTo, map[string]struct{}{})
		if ret.IsErr() {
			return ast.StmtErrRet(stmt, ret.String()).AddExtraInfo(fmt.Sprintf("in obj equal to %s", objEqualTo))
		}

		// 定义新对象及其等式关系
		equalFact := ast.NewEqualFact(ast.Atom(objName), objEqualTo)
		objInSetFact := ast.NewInFact(objName, objSet)
		stmtForDef := ast.NewDefLetStmt([]string{objName}, []ast.Obj{objSet}, []ast.FactStmt{equalFact}, stmt.Line)

		retStmt := exec.Env.DefLetStmt(stmtForDef)
		if retStmt.IsErr() {
			return ast.StmtErrRet(stmt, retStmt.String())
		}

		// 收集定义消息
		defineMsgs = append(defineMsgs, glob.IsANewObjectMsg(objName))
		defineMsgs = append(defineMsgs, equalFact.String())
		defineMsgs = append(defineMsgs, objInSetFact.String())

	}

	return exec.NewTrueStmtRet(stmt).AddNewFacts(newFactMsgs).AddDefineMsgs(defineMsgs).AddVerifyProcesses(verifyProcessMsgs)
}

func (exec *Executor) haveObjInNonEmptySetStmt(stmt *ast.HaveObjInNonEmptySetStmt) ast.StmtRet {
	defineMsgs := []string{}
	verifyProcessMsgs := []ast.VerRet{}

	for i := range len(stmt.Objs) {
		if !glob.IsKeywordSetOrNonEmptySetOrFiniteSet(stmt.ObjSets[i].String()) {
			existInFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIsANonEmptySet), []ast.Obj{stmt.ObjSets[i]}, stmt.Line)
			verifier := NewVerifier(exec.Env)
			verRet := verifier.VerFactStmt(existInFact, Round0Msg())
			if verRet.IsNotTrue() {
				return ast.StmtErrRet(stmt, verRet.String())
			}

			verifyProcessMsgs = append(verifyProcessMsgs, verRet)
		}

		stmtForDef := ast.NewDefLetStmt([]string{stmt.Objs[i]}, []ast.Obj{stmt.ObjSets[i]}, []ast.FactStmt{}, stmt.Line)
		retStmt := exec.Env.DefLetStmt(stmtForDef)
		if retStmt.IsErr() {
			return ast.StmtErrRet(stmt, retStmt.String())
		}
		execRet := exec.NewTrueStmtRet(stmtForDef)
		if execRet.IsNotTrue() {
			return ast.StmtErrRet(stmt, fmt.Sprintf("%s\n", stmt.String())).AddExtraInfo(execRet.String())
		}

		inFact := ast.NewInFact(stmt.Objs[i], stmt.ObjSets[i])

		defineMsgs = append(defineMsgs, glob.IsANewObjectMsg(stmt.Objs[i]))
		defineMsgs = append(defineMsgs, inFact.String())
	}

	return ast.NewTrueStmtEmptyRet(stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
	// return exec.AddStmtToStmtRet(ast.NewTrueStmtEmptyRet(nil), stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) haveFnEqualStmt(stmt *ast.HaveFnEqualStmt) ast.StmtRet {
	shortRet := checkParamsInFnDefNotDefinedAndParamSetsDefined(exec, stmt.DefHeader.Params, stmt.DefHeader.ParamSets)
	if shortRet.IsNotTrue() {
		return ast.StmtErrRet(stmt, shortRet.String())
	}

	verifyProcessMsgs := []ast.VerRet{}
	defineMsgs := []string{}

	// 返回值要是set
	execState := exec.factStmt(ast.NewIsASetFact(stmt.RetSet, stmt.Line))
	if execState.IsNotTrue() {
		return ast.StmtErrRet(stmt, execState.String())
	}
	if execState.IsUnknown() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("return set %s must be a set, i.e. `%s in set` must be true, but it is unknown", stmt.RetSet.String(), stmt.RetSet.String()))
	}

	execRet := exec.checkFnEqualStmt(stmt)
	if execRet.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(execRet.String())
		// return exec.AddStmtToStmtRet(execRet, stmt)
	}
	if trueRet, ok := execRet.(*ast.TrueStmtRet); ok {
		verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
	}

	newFnDefStmt := ast.NewLetFnStmt(string(stmt.DefHeader.Name), ast.NewFnTStruct(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, stmt.RetSet, []ast.FactStmt{}, []ast.FactStmt{ast.NewEqualFact(fnHeaderToReturnValueOfFn(stmt.DefHeader), stmt.EqualTo)}, stmt.Line), stmt.Line)
	execRet = exec.lefDefFnStmt(newFnDefStmt)
	if execRet.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(execRet.String()).AddExtraInfo(fmt.Sprintf("failed to declare fn: %s", newFnDefStmt.String()))
		// return exec.AddStmtToStmtRet(execRet.AddExtraInfo(fmt.Sprintf("failed to declare fn: %s", newFnDefStmt.String())), stmt)
	}
	defineMsgs = append(defineMsgs, newFnDefStmt.String())

	return ast.NewTrueStmtEmptyRet(stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
	// return exec.AddStmtToStmtRet(ast.NewTrueStmtEmptyRet(nil), stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) checkFnEqualStmt(stmt *ast.HaveFnEqualStmt) ast.StmtRet {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	for i := range len(stmt.DefHeader.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefHeader.Params[i]}, []ast.Obj{stmt.DefHeader.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState
		}
	}

	// Check if equalTo is defined
	ver := NewVerifier(exec.Env)
	verRet := ver.objIsDefinedAtomOrIsFnSatisfyItsReq(stmt.EqualTo, Round0NoMsg())
	if verRet.IsNotTrue() {
		return verRet.ToStmtRet()
	}

	// Execute proof
	for _, proofStmt := range stmt.Proofs {
		execState := exec.Stmt(proofStmt)
		if execState.IsNotTrue() {
			return execState
		}
	}

	// Verify return value is in retSet
	execState := exec.factStmt(ast.NewInFactWithObj(stmt.EqualTo, stmt.RetSet))
	if execState.IsErr() {
		return execState
	}
	if execState.IsUnknown() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("according to the definition of %s, the returned value %s must be in %s, but\n%s is unknown", stmt, stmt.EqualTo, stmt.RetSet, ast.NewInFactWithObj(stmt.EqualTo, stmt.RetSet)))
	}

	return exec.NewTrueStmtRet(stmt)
}

func fnHeaderToReturnValueOfFn(head *ast.DefHeader) ast.Obj {
	params := make([]ast.Obj, len(head.Params))
	for i := range len(head.Params) {
		params[i] = ast.Atom(head.Params[i])
	}

	fnName := ast.Atom(head.Name)

	return ast.NewFnObj(fnName, params)
}

func (exec *Executor) haveFnStmt(stmt *ast.HaveFnStmt) ast.StmtRet {
	shortRet := checkParamsInFnDefNotDefinedAndParamSetsDefined(exec, stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets)
	if shortRet.IsNotTrue() {
		return ast.StmtErrRet(stmt, shortRet.String())
	}

	verifyProcessMsgs := []ast.VerRet{}
	defineMsgs := []string{}

	// Verify first
	execRet := exec.checkHaveFnStmt(stmt)
	if execRet.IsNotTrue() {
		return execRet
	}
	if trueRet, ok := execRet.(*ast.TrueStmtRet); ok {
		verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
	}

	execRet = exec.lefDefFnStmt(stmt.DefFnStmt)

	if execRet.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(execRet.String())
		// return exec.AddStmtToStmtRet(execRet, stmt)
	}

	defineMsgs = append(defineMsgs, stmt.DefFnStmt.String())

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) checkHaveFnStmt(stmt *ast.HaveFnStmt) ast.StmtRet {
	// Create a new environment for verification and proof
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// 声明一下函数，这样证明then的时候不会因为没声明这个函数而g了
	localTemplate := ast.NewFnTStruct(stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets, stmt.DefFnStmt.FnTemplate.RetSet, stmt.DefFnStmt.FnTemplate.DomFacts, []ast.FactStmt{}, stmt.Line)
	fnDefStmt := ast.NewLetFnStmt(stmt.DefFnStmt.Name, localTemplate, stmt.Line)
	execState := exec.lefDefFnStmt(fnDefStmt)
	if execState.IsNotTrue() {
		return execState
	}

	// Verify retSet is in set type
	execState = exec.factStmt(ast.NewIsASetFact(stmt.DefFnStmt.FnTemplate.RetSet, stmt.Line))
	if execState.IsErr() {
		return execState
	}
	if execState.IsUnknown() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("return set (%s) must be a set, i.e. `%s in set` must be true, but it is unknown", stmt.DefFnStmt.FnTemplate.RetSet.String(), stmt.DefFnStmt.FnTemplate.RetSet.String()))
	}

	// Define parameters in the new environment
	defObjStmt := ast.NewDefLetStmt(stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets, stmt.DefFnStmt.FnTemplate.DomFacts, stmt.Line)
	execState = exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	// Execute proof statements
	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState
		}
	}

	// Verify that HaveObjSatisfyFn is in the return set
	execState = exec.factStmt(ast.NewInFactWithObj(stmt.HaveObjSatisfyFn, stmt.DefFnStmt.FnTemplate.RetSet))
	if execState.IsNotTrue() {
		return execState
	}

	// // 声明一下函数，这样证明then的时候不会因为没声明这个函数而g了
	// localTemplate := ast.NewFnTStruct(stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets, stmt.DefFnStmt.FnTemplate.RetSet, stmt.DefFnStmt.FnTemplate.DomFacts, []ast.FactStmt{}, stmt.Line)
	// fnDefStmt := ast.NewLetFnStmt(stmt.DefFnStmt.Name, localTemplate, stmt.Line)
	// execState = exec.lefDefFnStmt(fnDefStmt)
	// if execState.IsNotTrue() {
	// 	return execState
	// }

	// know 一下 函数等于 等号右边的东西
	params := []ast.Obj{}
	for i := range len(stmt.DefFnStmt.FnTemplate.Params) {
		params = append(params, ast.Atom(stmt.DefFnStmt.FnTemplate.Params[i]))
	}

	fnObj := ast.NewFnObj(ast.Atom(stmt.DefFnStmt.Name), params)
	fnObjIsEqualTo := ast.NewEqualFact(fnObj, stmt.HaveObjSatisfyFn)
	retInfer := exec.Env.NewFactWithCheckingNameDefined(fnObjIsEqualTo)
	if retInfer.IsErr() {
		return ast.StmtErrRet(stmt, retInfer.String())
	}

	// 证明 fn then 里全是对的
	for _, thenFact := range stmt.DefFnStmt.FnTemplate.ThenFacts {
		execState = exec.factStmt(thenFact)
		if execState.IsNotTrue() {
			return execState
		}
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) haveFnCaseByCaseStmt(stmt *ast.HaveFnCaseByCaseStmt) ast.StmtRet {
	shortRet := checkParamsInFnDefNotDefinedAndParamSetsDefined(exec, stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets)
	if shortRet.IsNotTrue() {
		return ast.StmtErrRet(stmt, shortRet.String())
	}

	verifyProcessMsgs := []ast.VerRet{}
	defineMsgs := []string{}
	// Verify first and get thenFacts
	execRet := exec.checkHaveFnCaseByCaseStmt(stmt)
	if execRet.IsNotTrue() {
		return execRet
	}
	if trueRet, ok := execRet.(*ast.TrueStmtRet); ok {
		verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
	}
	// Only after all verifications pass, declare the function
	execRet = exec.lefDefFnStmt(stmt.DefFnStmt)
	if execRet.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(execRet.String())
		// return exec.AddStmtToStmtRet(execRet, stmt)
	}
	defineMsgs = append(defineMsgs, stmt.DefFnStmt.String())
	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) checkHaveFnCaseByCaseStmt(stmt *ast.HaveFnCaseByCaseStmt) ast.StmtRet {
	verifyProcessMsgs := []ast.VerRet{}

	// Verify all cases cover domain and don't overlap
	execState := exec.haveFnCaseByCase_AllCasesCoverDomainAndNotOverlap(stmt)
	if execState.IsNotTrue() {
		return execState
	}
	if trueRet, ok := execState.(*ast.TrueStmtRet); ok {
		verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
	}

	// Verify each case: execute proof and verify return value
	execState = exec.checkHaveFnCaseByCaseStmt_Cases(stmt)
	if execState.IsNotTrue() {
		return execState
	}
	if trueRet, ok := execState.(*ast.TrueStmtRet); ok {
		verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
	}

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs)
}

func (exec *Executor) haveFnCaseByCase_AllCasesCoverDomainAndNotOverlap(stmt *ast.HaveFnCaseByCaseStmt) ast.StmtRet {
	return exec.verifyCasesOrAndNoOverlap(stmt.CaseByCaseFacts, stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets, stmt.ProveCases, stmt.Line)
}

func (exec *Executor) checkHaveFnCaseByCaseStmt_Cases(stmt *ast.HaveFnCaseByCaseStmt) ast.StmtRet {
	verifyProcessMsgs := []ast.VerRet{}
	// Verify each case: execute proof and verify return value
	for i := range len(stmt.CaseByCaseFacts) {
		execState := exec.verifyHaveFnCaseByCase_OneCase(stmt, i)
		if execState.IsNotTrue() {
			return execState
		}
		if trueRet, ok := execState.(*ast.TrueStmtRet); ok {
			verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
		}
	}

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs)
}

func (exec *Executor) verifyHaveFnCaseByCase_OneCase(stmt *ast.HaveFnCaseByCaseStmt, caseIndex int) ast.StmtRet {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// Define parameters
	defObjStmt := ast.NewDefLetStmt(
		stmt.DefFnStmt.FnTemplate.Params,
		stmt.DefFnStmt.FnTemplate.ParamSets,
		stmt.DefFnStmt.FnTemplate.DomFacts,
		stmt.Line,
	)
	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return ast.StmtErrRet(stmt, execState.String())
	}

	// Add case condition as fact
	caseFact := stmt.CaseByCaseFacts[caseIndex]
	retInfer := exec.Env.NewFactWithCheckingNameDefined(caseFact)
	if retInfer.IsErr() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("case %d: failed to add case fact: %s", caseIndex, retInfer.String()))
	}

	// Execute proof for this case
	for _, proof := range stmt.Proofs[caseIndex] {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return ast.StmtErrRet(stmt, fmt.Sprintf("case %d: proof failed", caseIndex))
		}
	}

	// Verify return value is in retSet
	equalTo := stmt.EqualToObjs[caseIndex]
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(ast.NewInFactWithObj(equalTo, stmt.DefFnStmt.FnTemplate.RetSet), Round0Msg())
	if verRet.IsErr() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("case %d: %s", caseIndex, verRet.String()))
	}
	if verRet.IsUnknown() {
		return ast.NewUnknownStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("case %d: according to the definition of %s, when %s is true, the returned value %s must be in %s, but\n%s is unknown", caseIndex, stmt, caseFact, equalTo, stmt.DefFnStmt.FnTemplate.RetSet, ast.NewInFactWithObj(equalTo, stmt.DefFnStmt.FnTemplate.RetSet)))
	}

	// The proof statements should have established the necessary conditions
	// Note: We don't verify thenFacts here because the function is not yet defined,
	// and object substitution (ReplaceObj) is not currently available.
	// The proof statements in each case should prove what's needed.

	return exec.NewTrueStmtRet(stmt)
}

// verifyCasesOrAndNoOverlap is a helper function to verify both:
// 1. cases cover all possibilities (or cases holds)
// 2. cases don't overlap
// If proveOr is provided and non-empty, it executes the proof in a local environment, then verifies both conditions.
// Otherwise, it verifies both conditions directly.
func (exec *Executor) verifyCasesOrAndNoOverlap(caseFacts ast.SpecFactPtrSlice, params ast.StrSlice, paramSets ast.ObjSlice, proveOr ast.StmtSlice, line uint) ast.StmtRet {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// Define parameters
	for i := range len(params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{params[i]}, []ast.Obj{paramSets[i]}, []ast.FactStmt{}, line))
		if execState.IsNotTrue() {
			return ast.StmtErrRet(nil, execState.String())
		}
	}

	// If proveOr is provided, execute it
	if len(proveOr) > 0 {
		for _, proofStmt := range proveOr {
			execState := exec.Stmt(proofStmt)
			if execState.IsNotTrue() {
				return ast.StmtErrRet(nil, fmt.Sprintf("prove or: proof failed: %s", execState.String()))
			}
		}
	}

	// Otherwise, verify both conditions directly
	// 1. Verify or cases holds
	orFact := ast.NewOrStmt(caseFacts, line)
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(orFact, Round0Msg())
	if verRet.IsErr() {
		return ast.StmtErrRet(nil, fmt.Sprintf("failed to verify that all cases cover the domain: %s", verRet.String()))
	}
	if verRet.IsUnknown() {
		return ast.NewUnknownStmtEmptyRet(nil).AddExtraInfo(fmt.Sprintf("all cases must cover the entire domain, i.e., %s must be true, but it is unknown", orFact))
	}

	// 2. Verify all cases don't overlap
	for i := range len(caseFacts) {
		execState := exec.verifyCaseNoOverlapWithOthers(caseFacts, i)
		if execState.IsNotTrue() {
			return execState
		}
	}

	return exec.NewTrueStmtRet(orFact)
}

// verifyCasesOr is a helper function to verify that cases cover all possibilities
// Deprecated: Use verifyCasesOrAndNoOverlap instead
// func (exec *Executor) verifyCasesOr(caseFacts ast.SpecFactPtrSlice, params ast.StrSlice, paramSets ast.ObjSlice, proveOr ast.StmtSlice, line uint) (ast.StmtRet, error) {
// 	exec.NewEnv()
// 	defer func() {
// 		exec.deleteEnv()
// 	}()

// 	// Define parameters
// 	for i := range len(params) {
// 		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{params[i]}, []ast.Obj{paramSets[i]}, []ast.FactStmt{}, line))
// 		if execState.IsNotTrue() {
// 			return execState, fmt.Errorf(execState.String())
// 		}
// 	}

// 	// If proveOr is provided, execute it
// 	if len(proveOr) > 0 {
// 		for _, proofStmt := range proveOr {
// 			execState := exec.Stmt(proofStmt)
// 			if execState.IsNotTrue() {
// 				return execState, fmt.Errorf("prove or: proof failed: %s", execState.String())
// 			}
// 		}
// 		// After executing proof, verify the or fact is true
// 		orFact := ast.NewOrStmt(caseFacts, line)
// 		execState := exec.factStmt(orFact)
// 		if execState.IsErr() {
// 			return glob.NewEmptyStmtError(), fmt.Errorf("prove or: failed to verify that all cases cover the domain: %s", execState.String())
// 		}
// 		if execState.IsUnknown() {
// 			return glob.NewEmptyStmtError(), fmt.Errorf("prove or: all cases must cover the entire domain, i.e., %s must be true, but it is unknown", orFact)
// 		}
// 		return exec.NewTrueStmtRet(orFact), nil
// 	}

// 	// Otherwise, verify the or fact directly
// 	orFact := ast.NewOrStmt(caseFacts, line)
// 	ver := NewVerifier(exec.Env)
// 	verRet := ver.VerFactStmt(orFact, Round0Msg())
// 	if verRet.IsErr() {
// 		return glob.NewEmptyStmtError(), fmt.Errorf("failed to verify that all cases cover the domain: %s", verRet.String())
// 	}
// 	if verRet.IsUnknown() {
// 		return glob.NewEmptyStmtError(), fmt.Errorf("all cases must cover the entire domain, i.e., %s must be true, but it is unknown", orFact)
// 	}

// 	return exec.NewTrueStmtRet(orFact), nil
// }

// verifyCasesNoOverlap is a helper function to verify that cases don't overlap
// Deprecated: Use verifyCasesOrAndNoOverlap instead
// func (exec *Executor) verifyCasesNoOverlap(caseFacts ast.SpecFactPtrSlice, params ast.StrSlice, paramSets ast.ObjSlice, proveOr ast.StmtSlice, line uint) (ast.StmtRet, error) {
// 	exec.NewEnv()
// 	defer func() {
// 		exec.deleteEnv()
// 	}()

// 	// Define parameters
// 	for i := range len(params) {
// 		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{params[i]}, []ast.Obj{paramSets[i]}, []ast.FactStmt{}, line))
// 		if execState.IsNotTrue() {
// 			return execState, fmt.Errorf(execState.String())
// 		}
// 	}

// 	// If proveOr is provided, execute it
// 	if len(proveOr) > 0 {
// 		for _, proofStmt := range proveOr {
// 			execState := exec.Stmt(proofStmt)
// 			if execState.IsNotTrue() {
// 				return execState, fmt.Errorf("prove or: proof failed: %s", execState.String())
// 			}
// 		}

// 		// After executing proof, verify 1. or cases holds
// 		orFact := ast.NewOrStmt(caseFacts, line)
// 		execState := exec.factStmt(orFact)
// 		if execState.IsErr() {
// 			return glob.NewEmptyStmtError(), fmt.Errorf("prove or: failed to verify that all cases cover the domain: %s", execState.String())
// 		}
// 		if execState.IsUnknown() {
// 			return glob.NewEmptyStmtError(), fmt.Errorf("prove or: all cases must cover the entire domain, i.e., %s must be true, but it is unknown", orFact)
// 		}
// 	}

// 	// Verify 2. all cases don't overlap
// 	// For each case i, verify that when case i holds, all other cases don't hold
// 	// If proveOr was provided, we need to run it again in each case's environment
// 	for i := range len(caseFacts) {
// 		execState, err := exec.verifyCaseNoOverlapWithOthers(caseFacts, proveOr, i)
// 		if notOkExec(execState, err) {
// 			return execState, err
// 		}
// 	}

// 	orFact := ast.NewOrStmt(caseFacts, line)
// 	return exec.NewTrueStmtRet(orFact), nil
// }

// verifyCaseNoOverlapWithOthers verifies that when case i holds, all other cases don't hold
// If proveOr is provided, it runs proveOr in the new environment before verifying
func (exec *Executor) verifyCaseNoOverlapWithOthers(caseFacts ast.SpecFactPtrSlice, caseIndex int) ast.StmtRet {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// Assume current case condition holds
	caseFact := caseFacts[caseIndex]
	retInfer := exec.Env.NewFactWithCheckingNameDefined(caseFact)
	if retInfer.IsErr() {
		return ast.StmtErrRet(nil, fmt.Sprintf("case %d: failed to add case fact: %s", caseIndex, retInfer.String()))
	}

	// Verify all other cases don't hold
	ver := NewVerifier(exec.Env)
	for j := range len(caseFacts) {
		if j == caseIndex {
			continue
		}

		// Get not case j
		otherCaseFact := caseFacts[j]
		notOtherCaseFacts := otherCaseFact.ReverseIsTrue()

		for _, notOtherCaseFact := range notOtherCaseFacts {
			// Verify not case j is true
			verRet := ver.VerFactStmt(notOtherCaseFact, Round0Msg())
			if verRet.IsErr() {
				msg := fmt.Sprintf("case %d and case %d overlap: failed to verify that not %s: %s", caseIndex, j, otherCaseFact, verRet.String())
				return ast.StmtErrRet(nil, msg)
			}
			if verRet.IsUnknown() {
				msg := fmt.Sprintf("case %d and case %d overlap: when %s is true, %s must be true, but it is unknown", caseIndex, j, caseFact, notOtherCaseFact)
				return ast.NewUnknownStmtEmptyRet(nil).AddExtraInfo(msg)
			}
		}
	}

	return exec.NewTrueStmtRet(caseFact)
}

func (exec *Executor) haveObjStStmt(stmt *ast.HaveObjStStmt) ast.StmtRet {
	existStFact := stmt.ToTruePurePropExistStFact()
	retStmt := exec.factStmt(existStFact)
	if retStmt.IsUnknown() || retStmt.IsErr() {
		verifyProcessMsgs := []ast.VerRet{}
		if trueRet, ok := retStmt.(*ast.TrueStmtRet); ok {
			verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
		}
		return exec.NewErrStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs)
	}

	// define
	retStmt2 := exec.Env.DefLetStmt(ast.NewDefLetStmt(stmt.ObjNames, stmt.ObjSets, []ast.FactStmt{stmt.Fact}, stmt.Line))
	if retStmt2.IsErr() {
		return exec.NewTrueStmtRet(stmt).AddExtraInfos(retStmt2.GetExtraInfos())
	}
	if retStmt2.IsUnknown() {
		return exec.NewTrueStmtRet(stmt).AddExtraInfos(retStmt2.GetExtraInfos())
	}

	defineMsgs := []string{}
	inferRets := []ast.InferRet{}
	if trueRet, ok := retStmt2.(*ast.TrueStmtRet); ok {
		defineMsgs = trueRet.Define
		inferRets = trueRet.Infer
	}

	return exec.NewTrueStmtRet(stmt).AddDefineMsgs(defineMsgs).AddInfers(inferRets)
}
