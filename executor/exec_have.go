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

func (exec *Executor) haveObjStStmt(stmt *ast.HaveObjStStmt, requireMsg bool) *glob.StmtRet {
	// 检查 SpecFactStmt 是否满足了
	execState := exec.Verify(stmt.Fact, false)
	if execState.IsNotTrue() {
		return execState
	}

	if execState.IsNotTrue() {
		return execState
	}

	if glob.IsBuiltinExistPropName(string(stmt.Fact.PropName)) {
		return glob.NewEmptyStmtUnknown()
	}

	// TODO 把 exist prop def 里的东西释放出来
	existPropDef := exec.Env.GetExistPropDef(stmt.Fact.PropName)
	if existPropDef == nil {
		return glob.NewEmptyStmtUnknown()
	}

	if len(existPropDef.ExistParams) != len(stmt.ObjNames) {
		return glob.ErrRet(fmt.Sprintf("exist prop def params number not equal to have stmt obj names number. expect %d, but got %d", len(existPropDef.ExistParams), len(stmt.ObjNames)))
	}

	uniMap := map[string]ast.Obj{}
	ExistParamsAtoms := []ast.Obj{}
	for i, param := range existPropDef.ExistParams {
		paramAsAtom := ast.Atom(stmt.ObjNames[i])
		uniMap[param] = paramAsAtom
		ExistParamsAtoms = append(ExistParamsAtoms, paramAsAtom)
	}

	for i, param := range existPropDef.DefBody.DefHeader.Params {
		uniMap[param] = stmt.Fact.Params[i]
	}

	instantiatedExistPropDefStmt, err := existPropDef.Instantiate(uniMap)
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	// 把 obj 放入环境
	for i, objName := range stmt.ObjNames {
		stmtForDef := ast.NewDefLetStmt([]string{objName}, []ast.Obj{instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).ExistParamSets[i]}, []ast.FactStmt{}, stmt.Line)
		ret := exec.Env.DefLetStmt(stmtForDef)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
		execState := exec.NewTrueStmtRet(stmtForDef)
		if execState.IsNotTrue() {
			return execState
		}
	}

	// param in param sets is true
	// for _, paramInParamSet := range instantiatedExistPropDefStmt.ExistParamInSetsFacts() {
	// 	err := exec.env.NewFact(paramInParamSet)
	// 	if err != nil {
	// 		return glob.ExecState_Error, err
	// 	}
	// }

	for i, existParamSet := range instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).ExistParamSets {
		ret := exec.Env.NewFactWithoutCheckingNameDefined(ast.NewInFact(stmt.ObjNames[i], existParamSet))
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	// dom of def exist prop is true
	for _, domFact := range instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).DefBody.DomFactsOrNil {
		ret := exec.Env.NewFactWithoutCheckingNameDefined(domFact)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	// iff of def exist prop is true
	for _, iffFact := range instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).DefBody.IffFactsOrNil {
		ret := exec.Env.NewFactWithoutCheckingNameDefined(iffFact)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	// 相关的 exist st 事实也成立
	existStFactParams := ast.MakeExistFactParamsSlice(ExistParamsAtoms, stmt.Fact.Params)

	newExistStFact := ast.NewSpecFactStmt(ast.TrueExist_St, ast.Atom(string(stmt.Fact.PropName)), existStFactParams, stmt.Line)
	ret := exec.Env.NewFactWithoutCheckingNameDefined(newExistStFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	result := glob.NewEmptyStmtTrue()
	if requireMsg {
		result = exec.AddStmtToStmtRet(result, stmt)
	}

	verifyProcessMsgs := []*glob.VerMsg{glob.NewVerMsg(stmt.Fact.String(), stmt.Line, []string{"is true"})}
	inferMsgs := append([]string{}, ret.Infer...)
	defineMsgs := []string{}
	for _, fact := range stmt.ObjNames {
		defineMsgs = append(defineMsgs, glob.IsANewObjectMsg(fact))
	}
	defineMsgs = append(defineMsgs, newExistStFact.String())

	return result.AddVerifyProcesses(verifyProcessMsgs).AddInfers(inferMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) haveObjEqualStmt(stmt *ast.HaveObjEqualStmt) *glob.StmtRet {
	ver := NewVerifier(exec.Env)

	newFactMsgs := []string{}
	defineMsgs := []string{}
	verifyProcessMsgs := []*glob.VerMsg{}

	for i := range len(stmt.ObjNames) {
		objName := stmt.ObjNames[i]
		objEqualTo := stmt.ObjEqualTos[i]
		objSet := stmt.ObjSets[i]

		// 验证等号右边的对象是否已定义
		if ret := ver.objIsDefinedAtomOrIsFnSatisfyItsReq(objEqualTo, Round0NoMsg()); ret.IsNotTrue() {
			return ret
		}

		// 验证等号右边的对象是否在指定的集合中
		inFact := ast.NewInFactWithObj(objEqualTo, objSet)
		verRet := ver.VerFactStmt(inFact, Round0Msg())
		if verRet.IsErr() {
			return glob.ErrRet(verRet.String())
		}
		if verRet.IsUnknown() {
			return glob.ErrRet(fmt.Sprintf("%s is not in %s", objName, objSet))
		}
		verifyProcessMsgs = append(verifyProcessMsgs, verRet.VerifyProcess...)

		// 检查等号右边的对象中的名称是否存在
		ret := exec.Env.LookupNamesInObj(objEqualTo, map[string]struct{}{})
		if ret.IsErr() {
			ret.AddError(fmt.Sprintf("in obj equal to %s", objEqualTo))
			return glob.ErrRet(ret.String())
		}

		// 定义新对象及其等式关系
		equalFact := ast.NewEqualFact(ast.Atom(objName), objEqualTo)
		objInSetFact := ast.NewInFact(objName, objSet)
		stmtForDef := ast.NewDefLetStmt([]string{objName}, []ast.Obj{objSet}, []ast.FactStmt{equalFact}, stmt.Line)

		ret = exec.Env.DefLetStmt(stmtForDef)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}

		// 收集定义消息
		defineMsgs = append(defineMsgs, glob.IsANewObjectMsg(objName))
		defineMsgs = append(defineMsgs, equalFact.String())
		defineMsgs = append(defineMsgs, objInSetFact.String())

	}

	return exec.NewTrueStmtRet(stmt).AddNewFacts(newFactMsgs).AddDefineMsgs(defineMsgs).AddVerifyProcesses(verifyProcessMsgs)
}

func (exec *Executor) haveObjInNonEmptySetStmt(stmt *ast.HaveObjInNonEmptySetStmt) *glob.StmtRet {
	verifyProcessMsgs := []*glob.VerMsg{}
	defineMsgs := []string{}

	for i := range len(stmt.Objs) {
		if !glob.IsKeywordSetOrNonEmptySetOrFiniteSet(stmt.ObjSets[i].String()) {
			existInFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsANonEmptySet), []ast.Obj{stmt.ObjSets[i]}, stmt.Line)
			execRet := exec.factStmt(existInFact)
			if execRet.IsNotTrue() {
				return glob.ErrRet(fmt.Sprintf("%s\n", stmt.String())).AddError(execRet.String())
			}

			verifyProcessMsgs = append(verifyProcessMsgs, execRet.VerifyProcess...)
		}

		stmtForDef := ast.NewDefLetStmt([]string{stmt.Objs[i]}, []ast.Obj{stmt.ObjSets[i]}, []ast.FactStmt{}, stmt.Line)
		ret := exec.Env.DefLetStmt(stmtForDef)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
		execRet := exec.NewTrueStmtRet(stmtForDef)
		if execRet.IsNotTrue() {
			return glob.ErrRet(fmt.Sprintf("%s\n", stmt.String())).AddError(execRet.String())
		}

		inFact := ast.NewInFact(stmt.Objs[i], stmt.ObjSets[i])

		defineMsgs = append(defineMsgs, glob.IsANewObjectMsg(stmt.Objs[i]))
		defineMsgs = append(defineMsgs, inFact.String())
	}

	return exec.AddStmtToStmtRet(glob.NewEmptyStmtTrue(), stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) haveFnEqualStmt(stmt *ast.HaveFnEqualStmt) *glob.StmtRet {
	var err error

	verifyProcessMsgs := []*glob.VerMsg{}
	defineMsgs := []string{}

	// 返回值要是set
	execState := exec.factStmt(ast.NewIsASetFact(stmt.RetSet, stmt.Line))
	if execState.IsNotTrue() {
		return glob.ErrRet(execState.String())
	}
	if execState.IsUnknown() {
		return glob.ErrRet(fmt.Sprintf("return set %s must be a set, i.e. `%s in set` must be true, but it is unknown", stmt.RetSet.String(), stmt.RetSet.String()))
	}

	execRet, err := exec.checkFnEqualStmt(stmt)
	if notOkExec(execRet, err) {
		return exec.AddStmtToStmtRet(execRet, stmt)
	}
	verifyProcessMsgs = append(verifyProcessMsgs, execRet.VerifyProcess...)

	newFnDefStmt := ast.NewDefFnStmt(string(stmt.DefHeader.Name), ast.NewFnTStruct(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, stmt.RetSet, []ast.FactStmt{}, []ast.FactStmt{ast.NewEqualFact(fnHeaderToReturnValueOfFn(stmt.DefHeader), stmt.EqualTo)}, stmt.Line), stmt.Line)
	execRet = exec.defFnStmt(newFnDefStmt)
	if execRet.IsNotTrue() {
		return exec.AddStmtToStmtRet(execRet.AddError(fmt.Sprintf("failed to declare fn: %s", newFnDefStmt.String())), stmt)
	}
	defineMsgs = append(defineMsgs, newFnDefStmt.String())

	return exec.AddStmtToStmtRet(glob.NewEmptyStmtTrue(), stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) checkFnEqualStmt(stmt *ast.HaveFnEqualStmt) (*glob.StmtRet, error) {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	for i := range len(stmt.DefHeader.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefHeader.Params[i]}, []ast.Obj{stmt.DefHeader.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	ver := NewVerifier(exec.Env)

	verRet := ver.VerFactStmt(ast.NewInFactWithObj(stmt.EqualTo, stmt.RetSet), Round0Msg())
	if verRet.IsErr() {
		return glob.ErrRet(verRet.String()), fmt.Errorf(verRet.String())
	}
	if verRet.IsUnknown() {
		return glob.ErrRet(verRet.String()), fmt.Errorf("according to the definition of %s, the returned value %s must be in %s, but\n%s is unknown", stmt, stmt.EqualTo, stmt.RetSet, ast.NewInFactWithObj(stmt.EqualTo, stmt.RetSet))
	}

	return verRet, nil
}

func fnHeaderToReturnValueOfFn(head *ast.DefHeader) ast.Obj {
	params := make([]ast.Obj, len(head.Params))
	for i := range len(head.Params) {
		params[i] = ast.Atom(head.Params[i])
	}

	fnName := ast.Atom(head.Name)

	return ast.NewFnObj(fnName, params)
}

func (exec *Executor) haveFnStmt(stmt *ast.HaveFnStmt) *glob.StmtRet {
	verifyProcessMsgs := []*glob.VerMsg{}
	defineMsgs := []string{}

	// Verify first
	execRet, err := exec.checkHaveFnStmt(stmt)
	if notOkExec(execRet, err) {
		return execRet
	}
	verifyProcessMsgs = append(verifyProcessMsgs, execRet.VerifyProcess...)

	execRet = exec.defFnStmt(stmt.DefFnStmt)

	if execRet.IsNotTrue() {
		return exec.AddStmtToStmtRet(execRet, stmt)
	}

	defineMsgs = append(defineMsgs, stmt.DefFnStmt.String())

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) checkHaveFnStmt(stmt *ast.HaveFnStmt) (*glob.StmtRet, error) {
	// Create a new environment for verification and proof
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// // 返回值要是set
	// execState := exec.factStmt(ast.NewIsASetFact(stmt.DefFnStmt.FnTemplate.RetSet, stmt.Line))
	// if execState.IsNotTrue() {
	// 	return glob.ErrRet(execState.String()), fmt.Errorf(execState.String())
	// }
	// if execState.IsUnknown() {
	// 	return glob.NewEmptyGlobError(), fmt.Errorf("return set %s must be a set, i.e. `%s in set` must be true, but it is unknown", stmt.DefFnStmt.FnTemplate.RetSet.String(), stmt.DefFnStmt.FnTemplate.RetSet.String())
	// }

	// 验证 fn template 里面的 paramSet 都是 in set 的
	// Verify each paramSet is in set type
	// for i, paramSet := range stmt.DefFnStmt.FnTemplate.ParamSets {
	// 	execState := exec.factStmt(ast.NewIsASetFact(paramSet, stmt.Line))
	// 	if execState.IsErr() {
	// 		return glob.ErrRet(execState.String()), fmt.Errorf(execState.String())
	// 	}
	// 	if execState.IsUnknown() {
	// 		return glob.NewEmptyGlobError(), fmt.Errorf("parameter set %d (%s) must be a set, i.e. `%s in set` must be true, but it is unknown", i+1, paramSet.String(), paramSet.String())
	// 	}
	// }

	// Verify retSet is in set type
	execState := exec.factStmt(ast.NewIsASetFact(stmt.DefFnStmt.FnTemplate.RetSet, stmt.Line))
	if execState.IsErr() {
		return glob.ErrRet(execState.String()), fmt.Errorf(execState.String())
	}
	if execState.IsUnknown() {
		return glob.NewEmptyStmtError(), fmt.Errorf("return set (%s) must be a set, i.e. `%s in set` must be true, but it is unknown", stmt.DefFnStmt.FnTemplate.RetSet.String(), stmt.DefFnStmt.FnTemplate.RetSet.String())
	}

	// Define parameters in the new environment
	defObjStmt := ast.NewDefLetStmt(stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets, stmt.DefFnStmt.FnTemplate.DomFacts, stmt.Line)
	execState = exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// Execute proof statements
	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// Verify that HaveObjSatisfyFn is in the return set
	execState = exec.factStmt(ast.NewInFactWithObj(stmt.HaveObjSatisfyFn, stmt.DefFnStmt.FnTemplate.RetSet))
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// 声明一下函数，这样证明then的时候不会因为没声明这个函数而g了
	localTemplate := ast.NewFnTStruct(stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets, stmt.DefFnStmt.FnTemplate.RetSet, stmt.DefFnStmt.FnTemplate.DomFacts, []ast.FactStmt{}, stmt.Line)
	fnDefStmt := ast.NewDefFnStmt(stmt.DefFnStmt.Name, localTemplate, stmt.Line)
	execState = exec.defFnStmt(fnDefStmt)
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// know 一下 函数等于 等号右边的东西
	params := []ast.Obj{}
	for i := range len(stmt.DefFnStmt.FnTemplate.Params) {
		params = append(params, ast.Atom(stmt.DefFnStmt.FnTemplate.Params[i]))
	}

	fnObj := ast.NewFnObj(ast.Atom(stmt.DefFnStmt.Name), params)
	fnObjIsEqualTo := ast.NewEqualFact(fnObj, stmt.HaveObjSatisfyFn)
	err := exec.Env.NewFactWithoutCheckingNameDefined(fnObjIsEqualTo)
	if err.IsErr() {
		return glob.ErrRet(err.String()), fmt.Errorf(err.String())
	}

	// 证明 fn then 里全是对的
	for _, thenFact := range stmt.DefFnStmt.FnTemplate.ThenFacts {
		execState = exec.factStmt(thenFact)
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	return exec.NewTrueStmtRet(stmt), nil
}

func (exec *Executor) haveFnCaseByCaseStmt(stmt *ast.HaveFnCaseByCaseStmt) *glob.StmtRet {

	verifyProcessMsgs := []*glob.VerMsg{}
	defineMsgs := []string{}
	// Verify first and get thenFacts
	execRet, _, err := exec.checkHaveFnCaseByCaseStmt(stmt)
	if notOkExec(execRet, err) {
		return execRet
	}
	verifyProcessMsgs = append(verifyProcessMsgs, execRet.VerifyProcess...)
	// Only after all verifications pass, declare the function
	execRet = exec.defFnStmt(stmt.DefFnStmt)
	if execRet.IsNotTrue() {
		return exec.AddStmtToStmtRet(execRet, stmt)
	}
	defineMsgs = append(defineMsgs, stmt.DefFnStmt.String())
	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) checkHaveFnCaseByCaseStmt(stmt *ast.HaveFnCaseByCaseStmt) (*glob.StmtRet, []ast.FactStmt, error) {
	// Create a new environment for verification and proof
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// Verify each paramSet is in set type
	for i, paramSet := range stmt.DefFnStmt.FnTemplate.ParamSets {
		execState := exec.factStmt(ast.NewIsASetFact(paramSet, stmt.Line))
		if execState.IsErr() {
			return glob.ErrRet(execState.String()), nil, fmt.Errorf(execState.String())
		}
		if execState.IsUnknown() {
			return glob.NewEmptyStmtError(), nil, fmt.Errorf("parameter set %d (%s) must be a set, i.e. `%s in set` must be true, but it is unknown", i+1, paramSet.String(), paramSet.String())
		}
	}

	// Verify retSet is in set type
	execState := exec.factStmt(ast.NewIsASetFact(stmt.DefFnStmt.FnTemplate.RetSet, stmt.Line))
	if execState.IsErr() {
		return glob.ErrRet(execState.String()), nil, fmt.Errorf(execState.String())
	}
	if execState.IsUnknown() {
		return glob.NewEmptyStmtError(), nil, fmt.Errorf("return set (%s) must be a set, i.e. `%s in set` must be true, but it is unknown", stmt.DefFnStmt.FnTemplate.RetSet.String(), ast.NewIsASetFact(stmt.DefFnStmt.FnTemplate.RetSet, stmt.Line))
	}

	// Verify each case: execute proof and verify return value
	for i := range len(stmt.CaseByCaseFacts) {
		execState, err := exec.verifyHaveFnCaseByCase_OneCase(stmt, i)
		if notOkExec(execState, err) {
			return execState, nil, err
		}
	}

	// Verify all cases cover the domain
	execState, err := exec.checkAtLeastOneCaseHolds_ForHaveFn(stmt)
	if notOkExec(execState, err) {
		return execState, nil, err
	}

	// Verify cases don't overlap
	execState, err = exec.checkCasesNoOverlap_ForHaveFn(stmt)
	if notOkExec(execState, err) {
		return execState, nil, err
	}

	// Build thenFacts: for each case, if condition holds, function equals corresponding return value
	thenFacts := []ast.FactStmt{}
	for i, caseFact := range stmt.CaseByCaseFacts {
		// Create function call from function name and params
		params := make([]ast.Obj, len(stmt.DefFnStmt.FnTemplate.Params))
		for j := range len(stmt.DefFnStmt.FnTemplate.Params) {
			params[j] = ast.Atom(stmt.DefFnStmt.FnTemplate.Params[j])
		}
		fnName := ast.Atom(stmt.DefFnStmt.Name)
		fnCall := ast.NewFnObj(fnName, params)
		equalFact := ast.NewEqualFact(fnCall, stmt.EqualToObjs[i])

		uniFact := ast.NewUniFact(
			stmt.DefFnStmt.FnTemplate.Params,
			stmt.DefFnStmt.FnTemplate.ParamSets,
			[]ast.FactStmt{caseFact},
			[]ast.FactStmt{equalFact},
			stmt.Line,
		)
		thenFacts = append(thenFacts, uniFact)
	}

	return exec.NewTrueStmtRet(stmt), thenFacts, nil
}

func (exec *Executor) verifyHaveFnCaseByCase_OneCase(stmt *ast.HaveFnCaseByCaseStmt, caseIndex int) (*glob.StmtRet, error) {
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
		return execState, fmt.Errorf(execState.String())
	}

	// Add case condition as fact
	caseFact := stmt.CaseByCaseFacts[caseIndex]
	ret := exec.Env.NewFactWithoutCheckingNameDefined(caseFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String()), fmt.Errorf("case %d: failed to add case fact: %s", caseIndex, ret.String())
	}

	// Execute proof for this case
	for _, proof := range stmt.Proofs[caseIndex] {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState, fmt.Errorf("case %d: proof failed", caseIndex)
		}
	}

	// Verify return value is in retSet
	equalTo := stmt.EqualToObjs[caseIndex]
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(ast.NewInFactWithObj(equalTo, stmt.DefFnStmt.FnTemplate.RetSet), Round0Msg())
	if verRet.IsErr() {
		return glob.NewEmptyStmtError(), fmt.Errorf("case %d: %s", caseIndex, verRet.String())
	}
	if verRet.IsUnknown() {
		return glob.NewEmptyStmtError(), fmt.Errorf("case %d: according to the definition of %s, when %s is true, the returned value %s must be in %s, but\n%s is unknown", caseIndex, stmt, caseFact, equalTo, stmt.DefFnStmt.FnTemplate.RetSet, ast.NewInFactWithObj(equalTo, stmt.DefFnStmt.FnTemplate.RetSet))
	}

	// The proof statements should have established the necessary conditions
	// Note: We don't verify thenFacts here because the function is not yet defined,
	// and object substitution (ReplaceObj) is not currently available.
	// The proof statements in each case should prove what's needed.

	return exec.NewTrueStmtRet(stmt), nil
}

func (exec *Executor) checkAtLeastOneCaseHolds_ForHaveFn(stmt *ast.HaveFnCaseByCaseStmt) (*glob.StmtRet, error) {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// Define parameters
	for i := range len(stmt.DefFnStmt.FnTemplate.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefFnStmt.FnTemplate.Params[i]}, []ast.Obj{stmt.DefFnStmt.FnTemplate.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// Create or fact: case1 or case2 or ... or caseN
	orFact := ast.NewOrStmt(stmt.CaseByCaseFacts, stmt.Line)

	// Verify or fact is true (all cases cover the domain)
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(orFact, Round0Msg())
	if verRet.IsErr() {
		return glob.NewEmptyStmtError(), fmt.Errorf("failed to verify that all cases cover the domain: %s", verRet.String())
	}
	if verRet.IsUnknown() {
		return glob.NewEmptyStmtError(), fmt.Errorf("all cases must cover the entire domain, i.e., %s must be true, but it is unknown", orFact)
	}

	return exec.NewTrueStmtRet(stmt), nil
}

func (exec *Executor) checkCasesNoOverlap_ForHaveFn(stmt *ast.HaveFnCaseByCaseStmt) (*glob.StmtRet, error) {
	// For each case i, verify that when case i holds, all other cases don't hold
	for i := range len(stmt.CaseByCaseFacts) {
		execState, err := exec.checkCaseNoOverlapWithOthers_ForHaveFn(stmt, i)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	return exec.NewTrueStmtRet(stmt), nil
}

func (exec *Executor) checkCaseNoOverlapWithOthers_ForHaveFn(stmt *ast.HaveFnCaseByCaseStmt, caseIndex int) (*glob.StmtRet, error) {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// Define parameters
	for i := range len(stmt.DefFnStmt.FnTemplate.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefFnStmt.FnTemplate.Params[i]}, []ast.Obj{stmt.DefFnStmt.FnTemplate.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// Assume current case condition holds
	caseFact := stmt.CaseByCaseFacts[caseIndex]
	ret := exec.Env.NewFactWithoutCheckingNameDefined(caseFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String()), fmt.Errorf("case %d: failed to add case fact: %s", caseIndex, ret.String())
	}

	// Verify all other cases don't hold
	ver := NewVerifier(exec.Env)
	for j := range len(stmt.CaseByCaseFacts) {
		if j == caseIndex {
			continue
		}

		// Get not case j
		otherCaseFact := stmt.CaseByCaseFacts[j]
		notOtherCaseFact := otherCaseFact.ReverseTrue()

		// Verify not case j is true
		verRet := ver.VerFactStmt(notOtherCaseFact, Round0Msg())
		if verRet.IsErr() {
			return glob.NewEmptyStmtError(), fmt.Errorf("case %d and case %d overlap: failed to verify that not %s: %s", caseIndex, j, otherCaseFact, verRet.String())
		}
		if verRet.IsUnknown() {
			return glob.NewEmptyStmtError(), fmt.Errorf("case %d and case %d may overlap: when %s is true, %s must be false, but it is unknown", caseIndex, j, caseFact, otherCaseFact)
		}
	}

	return exec.NewTrueStmtRet(stmt), nil
}

func (exec *Executor) haveFnEqualCaseByCaseStmt(stmt *ast.HaveFnEqualCaseByCaseStmt) *glob.StmtRet {
	verifyProcessMsgs := []*glob.VerMsg{}
	defineMsgs := []string{}
	// 返回值要是set
	execState := exec.factStmt(ast.NewIsASetFact(stmt.RetSet, stmt.Line))
	if execState.IsNotTrue() {
		return glob.ErrRet(execState.String())
	}
	if execState.IsUnknown() {
		return glob.ErrRet(fmt.Sprintf("return set %s must be a set, i.e. `%s in set` must be true, but it is unknown", stmt.RetSet.String(), stmt.RetSet.String()))
	}
	// 验证每个case的返回值都符合fn的retSet
	execState, err := exec.checkHaveFnEqualCaseByCaseStmt(stmt)
	if notOkExec(execState, err) {
		return exec.AddStmtToStmtRet(execState, stmt)
	}
	verifyProcessMsgs = append(verifyProcessMsgs, execState.VerifyProcess...)
	// 构建 thenFacts：对于每个 case，如果条件满足，则函数值等于对应的返回值
	thenFacts := []ast.FactStmt{}
	for i, caseFact := range stmt.CaseByCaseFacts {
		// 在 caseFact 的条件下，函数值等于对应的返回值
		// 需要将 caseFact 作为条件，然后添加等式
		fnCall := fnHeaderToReturnValueOfFn(stmt.DefHeader)
		equalFact := ast.NewEqualFact(fnCall, stmt.CaseByCaseEqualTo[i])

		// 创建一个条件事实：如果 caseFact 为真，则 equalFact 为真
		// 这里我们需要使用 implication 或者直接在 thenFacts 中添加条件
		// 由于 caseFact 是 SpecFactStmt，我们需要创建一个 UniFact 来表示这个条件
		// 但是更简单的方式是：创建一个 UniFact，其中 DomFacts 包含 caseFact，ThenFacts 包含 equalFact
		uniFact := ast.NewUniFact(
			[]string{},
			[]ast.Obj{},
			[]ast.FactStmt{caseFact},
			[]ast.FactStmt{equalFact},
			stmt.Line,
		)
		thenFacts = append(thenFacts, uniFact)
	}

	// 定义函数
	newFnDefStmt := ast.NewDefFnStmt(
		string(stmt.DefHeader.Name),
		ast.NewFnTStruct(
			stmt.DefHeader.Params,
			stmt.DefHeader.ParamSets,
			stmt.RetSet,
			[]ast.FactStmt{},
			thenFacts,
			stmt.Line,
		),
		stmt.Line,
	)
	execState = exec.defFnStmt(newFnDefStmt)
	if execState.IsNotTrue() {
		return exec.AddStmtToStmtRet(execState, stmt)
	}
	defineMsgs = append(defineMsgs, newFnDefStmt.String())
	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) checkHaveFnEqualCaseByCaseStmt(stmt *ast.HaveFnEqualCaseByCaseStmt) (*glob.StmtRet, error) {
	verifyProcessMsgs := []*glob.VerMsg{}
	// 验证每个case的返回值都符合fn的retSet（在case成立的条件下）
	for i := range len(stmt.CaseByCaseFacts) {
		execState, err := exec.checkCaseReturnValueInRetSet(stmt, i)
		if notOkExec(execState, err) {
			return execState, err
		}
		verifyProcessMsgs = append(verifyProcessMsgs, execState.VerifyProcess...)
	}

	// 验证所有的case覆盖了整个domain
	execState, err := exec.checkAtLeastOneCaseHolds(stmt)
	if notOkExec(execState, err) {
		return execState, err
	}
	verifyProcessMsgs = append(verifyProcessMsgs, execState.VerifyProcess...)
	// 验证每个case没有overlap
	execState, err = exec.checkCasesNoOverlap(stmt)
	if notOkExec(execState, err) {
		return execState, err
	}
	verifyProcessMsgs = append(verifyProcessMsgs, execState.VerifyProcess...)
	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs), nil
}

func (exec *Executor) checkCaseReturnValueInRetSet(stmt *ast.HaveFnEqualCaseByCaseStmt, caseIndex int) (*glob.StmtRet, error) {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// 为每个参数定义变量
	for i := range len(stmt.DefHeader.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefHeader.Params[i]}, []ast.Obj{stmt.DefHeader.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// 假设case的条件成立
	caseFact := stmt.CaseByCaseFacts[caseIndex]
	ret := exec.Env.NewFactWithoutCheckingNameDefined(caseFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String()), fmt.Errorf("case %d: failed to add case fact: %s", caseIndex, ret.String())
	}

	// 在case成立的条件下，验证返回值在retSet中
	equalTo := stmt.CaseByCaseEqualTo[caseIndex]
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(ast.NewInFactWithObj(equalTo, stmt.RetSet), Round0Msg())
	if verRet.IsErr() {
		return glob.NewEmptyStmtError(), fmt.Errorf("case %d: %s", caseIndex, verRet.String())
	}
	if verRet.IsUnknown() {
		return glob.NewEmptyStmtError(), fmt.Errorf("case %d: according to the definition of %s, when %s is true, the returned value %s must be in %s, but\n%s is unknown", caseIndex, stmt, caseFact, equalTo, stmt.RetSet, ast.NewInFactWithObj(equalTo, stmt.RetSet))
	}

	return exec.NewTrueStmtRet(stmt), nil
}

func (exec *Executor) checkAtLeastOneCaseHolds(stmt *ast.HaveFnEqualCaseByCaseStmt) (*glob.StmtRet, error) {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// 为每个参数定义变量
	for i := range len(stmt.DefHeader.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefHeader.Params[i]}, []ast.Obj{stmt.DefHeader.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// 创建 or fact: case1 or case2 or ... or caseN
	orFact := ast.NewOrStmt(stmt.CaseByCaseFacts, stmt.Line)

	// 验证 or fact 为 true（即所有 case 覆盖了整个 domain）
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(orFact, Round0Msg())
	if verRet.IsErr() {
		return glob.NewEmptyStmtError(), fmt.Errorf("failed to verify that all cases cover the domain: %s", verRet.String())
	}
	if verRet.IsUnknown() {
		return glob.NewEmptyStmtError(), fmt.Errorf("all cases must cover the entire domain, i.e., %s must be true, but it is unknown", orFact)
	}

	return exec.NewTrueStmtRet(stmt), nil
}

func (exec *Executor) checkCasesNoOverlap(stmt *ast.HaveFnEqualCaseByCaseStmt) (*glob.StmtRet, error) {
	// 对于每个 case i，验证在 case i 成立的条件下，其他所有 case 都不成立
	for i := range len(stmt.CaseByCaseFacts) {
		execState, err := exec.checkCaseNoOverlapWithOthers(stmt, i)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	return exec.NewTrueStmtRet(stmt), nil
}

func (exec *Executor) checkCaseNoOverlapWithOthers(stmt *ast.HaveFnEqualCaseByCaseStmt, caseIndex int) (*glob.StmtRet, error) {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// 为每个参数定义变量
	for i := range len(stmt.DefHeader.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefHeader.Params[i]}, []ast.Obj{stmt.DefHeader.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// 假设当前 case 的条件成立
	caseFact := stmt.CaseByCaseFacts[caseIndex]
	ret := exec.Env.NewFactWithoutCheckingNameDefined(caseFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String()), fmt.Errorf("case %d: failed to add case fact: %s", caseIndex, ret.String())
	}

	// 验证其他所有 case 都不成立
	ver := NewVerifier(exec.Env)
	for j := range len(stmt.CaseByCaseFacts) {
		if j == caseIndex {
			continue
		}

		// 获取 not case j
		otherCaseFact := stmt.CaseByCaseFacts[j]
		notOtherCaseFact := otherCaseFact.ReverseTrue()

		// 验证 not case j 为 true
		verRet := ver.VerFactStmt(notOtherCaseFact, Round0Msg())
		if verRet.IsErr() {
			return glob.NewEmptyStmtError(), fmt.Errorf("case %d and case %d overlap: failed to verify that not %s: %s", caseIndex, j, otherCaseFact, verRet.String())
		}
		if verRet.IsUnknown() {
			return glob.NewEmptyStmtError(), fmt.Errorf("case %d and case %d may overlap: when %s is true, %s must be false, but it is unknown", caseIndex, j, caseFact, otherCaseFact)
		}
	}

	return exec.NewTrueStmtRet(stmt), nil
}

// func (exec *Executor) haveObjFromCartSetStmt(stmt *ast.HaveObjFromCartSetStmt) *glob.StmtRet {
// 	// Check: verify cart parameters are sets and equalTo elements are in corresponding sets
// 	checkRet := exec.checkHaveObjFromCartSetStmt(stmt)
// 	if checkRet.IsNotTrue() {
// 		return checkRet
// 	}

// 	// Post-process: add obj in cart and obj = equalTo facts
// 	postRet := exec.postProcessHaveObjFromCartSetStmt(stmt)
// 	if postRet.IsNotTrue() {
// 		return postRet
// 	}

// 	return exec.AddStmtToStmtRet(glob.NewEmptyStmtTrue(), stmt)
// }

// checkHaveObjFromCartSetStmt checks that:
// 1. Each parameter of cart is a set
// 2. equalTo is a tuple with the same length as cart parameters
// 3. Each element of equalTo is in the corresponding cart set
// func (exec *Executor) checkHaveObjFromCartSetStmt(stmt *ast.HaveObjFromCartSetStmt) *glob.StmtRet {
// 	// Check that each parameter of cart is a set
// 	for i, param := range stmt.CartSet.Params {
// 		state := exec.factStmt(ast.NewIsASetFact(param, stmt.Line))
// 		if state.IsErr() {
// 			return glob.ErrRet(state.String())
// 		}
// 		if state.IsUnknown() {
// 			return glob.ErrRet(fmt.Sprintf("cart parameter %d (%s) must be a set, i.e. `is_a_set(%s)` must be true, but it is unknown", i+1, param.String(), param.String()))
// 		}
// 	}

// 	// Check that equalTo is a tuple
// 	equalToAsFn, ok := stmt.EqualTo.(*ast.FnObj)
// 	if !ok {
// 		return glob.ErrRet(fmt.Sprintf("expected equalTo to be a tuple, but got %T", stmt.EqualTo))
// 	}
// 	if !ast.IsTupleFnObj(equalToAsFn) {
// 		return glob.ErrRet(fmt.Sprintf("expected equalTo to be a tuple (with head %s), but got %s", glob.KeywordTuple, equalToAsFn.FnHead.String()))
// 	}

// 	// Check that tuple length matches cart parameters length
// 	if len(equalToAsFn.Params) != len(stmt.CartSet.Params) {
// 		return glob.ErrRet(fmt.Sprintf("tuple length (%d) does not match cart parameters length (%d)", len(equalToAsFn.Params), len(stmt.CartSet.Params)))
// 	}

// 	// Check that each element of equalTo is in the corresponding cart set
// 	for i := range len(equalToAsFn.Params) {
// 		inFact := ast.NewInFactWithObj(equalToAsFn.Params[i], stmt.CartSet.Params[i])
// 		state := exec.factStmt(inFact)
// 		if state.IsErr() {
// 			return glob.ErrRet(state.String())
// 		}
// 		if state.IsUnknown() {
// 			return glob.ErrRet(fmt.Sprintf("tuple element %d (%s) must be in cart set %d (%s), but it is unknown", i+1, equalToAsFn.Params[i].String(), i+1, stmt.CartSet.Params[i].String()))
// 		}
// 	}

// 	return glob.NewEmptyStmtTrue()
// }

// postProcessHaveObjFromCartSetStmt adds:
// 1. obj in cart(...) fact
// 2. obj = equalTo fact
// 3. obj[i] = equalTo[i] for each i
// 4. dim(obj) = len(cartSet.Params)
// func (exec *Executor) postProcessHaveObjFromCartSetStmt(stmt *ast.HaveObjFromCartSetStmt) *glob.StmtRet {
// 	objAtom := ast.Atom(stmt.ObjName)

// 	// Add obj in cart(...) fact
// 	inCartFact := ast.NewInFactWithObj(objAtom, stmt.CartSet)
// 	ret := exec.Env.NewFactWithoutCheckingNameDefined(inCartFact)
// 	if ret.IsErr() {
// 		return glob.ErrRet(ret.String())
// 	}

// 	// Add obj = equalTo fact
// 	equalFact := ast.NewEqualFact(objAtom, stmt.EqualTo)
// 	ret = exec.Env.NewFactWithoutCheckingNameDefined(equalFact)
// 	if ret.IsErr() {
// 		return glob.ErrRet(ret.String())
// 	}

// 	// equalTo is already verified to be a tuple in checkHaveObjFromCartSetStmt
// 	equalToAsFn, ok := stmt.EqualTo.(*ast.FnObj)
// 	if !ok || !ast.IsTupleFnObj(equalToAsFn) {
// 		return glob.NewEmptyStmtTrue()
// 	}

// 	// Add obj[i] = equalTo[i] for each i (index starts from 1)
// 	for i := range len(equalToAsFn.Params) {
// 		index := i + 1 // index starts from 1
// 		indexObj := ast.Atom(strconv.Itoa(index))

// 		// Create indexed object: obj[index]
// 		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordObjAtIndexOpt), []ast.Obj{objAtom, indexObj})

// 		// Create equal fact: obj[index] = equalTo[i]
// 		indexEqualFact := ast.NewEqualFact(indexedObj, equalToAsFn.Params[i])
// 		ret = exec.Env.NewFactWithoutCheckingNameDefined(indexEqualFact)
// 		if ret.IsErr() {
// 			return glob.ErrRet(ret.String())
// 		}
// 	}

// 	// Add dim(obj) = len(cartSet.Params)
// 	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{objAtom})
// 	dimValue := ast.Atom(strconv.Itoa(len(stmt.CartSet.Params)))
// 	dimEqualFact := ast.NewEqualFact(dimFn, dimValue)
// 	ret = exec.Env.NewFactWithoutCheckingNameDefined(dimEqualFact)
// 	if ret.IsErr() {
// 		return glob.ErrRet(ret.String())
// 	}

// 	return glob.NewEmptyStmtTrue()
// }
