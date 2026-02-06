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
)

func (exec *Executor) claimReversibleFactByContradiction(stmt *ast.ClaimProveByContradictionStmt) ast.StmtRet {
	innerStmtRets := []ast.StmtRet{}

	// know reverse of
	facts := stmt.ToCheckFact.(ast.Spec_OrFact).ReverseIsTrue()
	for _, curFact := range facts {
		inferRet := exec.Env.NewFactWithCheckingNameDefined(curFact)
		if inferRet.IsErr() {
			return ast.NewErrStmtEmptyRet(stmt).AddInfer(inferRet)
		}
	}

	for i := 0; i < len(stmt.Proofs)-1; i++ {
		curStmt := stmt.Proofs[i]
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("%s\nfailed :( line %d\n", curStmt.String(), curStmt.GetLine()))
		}
		innerStmtRets = append(innerStmtRets, execState)
	}

	lastStmtAsFact, ok := stmt.Proofs[len(stmt.Proofs)-1].(*ast.ImpossibleStmt)
	if !ok {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo("prove by contradiction only support impossible reversible fact as last statement")
	}

	reversedLastFact := lastStmtAsFact.Fact.ReverseIsTrue()

	reversedLastFactStr := []string{}
	for _, curFact := range reversedLastFact {
		reversedLastFactStr = append(reversedLastFactStr, curFact.String())
	}
	// reversedLastFactStrStr := strings.Join(reversedLastFactStr, "\n\t")

	for _, curFact := range reversedLastFact {
		execState := exec.factStmt(curFact)
		if execState.IsNotTrue() {
			return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(fmt.Sprintf("%s\nfailed :( line %d\n", curFact.String(), curFact.GetLine()))
		}
		innerStmtRets = append(innerStmtRets, execState)
	}

	return ast.NewTrueStmtEmptyRet(stmt).AddInnerStmtRets(innerStmtRets)
}

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) ast.StmtRet {
	// 需要检查stmt.ToCheckFact里的东西都是在外部声明好了的
	ret := exec.Env.LookUpNamesInFact(stmt.ToCheckFact, map[string]struct{}{})
	if ret.IsErr() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(ret.String())
	}

	switch stmt.ToCheckFact.(type) {
	case ast.Spec_OrFact:
		return exec.claimReversibleFactByContradiction(stmt)
	default:
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo("claim prove by contradiction only support reversible fact or forall fact")
	}
}

// func (exec *Executor) claimUniFactByContradiction(stmt *ast.ClaimProveByContradictionStmt) ast.StmtRet{
// 	asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt)
// 	if !ok {
// 		return ast.StmtErrRet(fmt.Sprintf("claim stmt prove uni fact only support uni fact"))
// 	}

// 	var thenFact ast.Spec_OrFact
// 	if len(asUnivFact.ThenFacts) == 1 {
// 		thenFact, ok = asUnivFact.ThenFacts[0].(ast.Spec_OrFact)
// 		if !ok {
// 			return ast.StmtErrRet(fmt.Sprintf("claim stmt prove uni fact only support forall fact with one then fact"))
// 		}
// 	} else {
// 		return ast.StmtErrRet(fmt.Sprintf("claim stmt prove uni fact only support forall fact with one then fact"))
// 	}

// 	exec.NewEnv()
// 	defer func() {
// 		exec.deleteEnv()
// 	}()

// 	execState := exec.declareParamsAndDomFactsInUniFact(asUnivFact)
// 	if execState.IsNotTrue() {
// 		return execState
// 	}

// 	reversedThenFact := thenFact.ReverseIsTrue()
// 	for _, curFact := range reversedThenFact {
// 		execState := exec.Env.NewFactWithCheckingNameDefined(curFact)
// 		if execState.IsNotTrue() {
// 			return execState
// 		}
// 	}

// 	innerStmtRets := []ast.StmtRet{}
// 	for i := 0; i < len(stmt.Proofs)-1; i++ {
// 		curStmt := stmt.Proofs[i]
// 		execState := exec.Stmt(curStmt)
// 		if execState.IsNotTrue() {
// 			return execState.AddError(fmt.Sprintf("%s\nfailed :( line %d\n", curStmt.String(), curStmt.GetLine()))
// 		}
// 		innerStmtRets = append(innerStmtRets, execState)
// 	}

// 	// 最后一位是impossible stmt
// 	lastStmtAsFact, ok := stmt.Proofs[len(stmt.Proofs)-1].(*ast.ImpossibleStmt)
// 	if !ok {
// 		return ast.StmtErrRet("prove by contradiction only support impossible reversible fact as last statement")
// 	}

// 	// 最后一位既对又错
// 	execState = exec.factStmt(lastStmtAsFact.Fact)
// 	if execState.IsNotTrue() {
// 		return execState
// 	}
// 	innerStmtRets = append(innerStmtRets, execState)

// 	// last fact is reversible
// 	reversedLastFact := lastStmtAsFact.Fact.ReverseIsTrue()
// 	for _, curFact := range reversedLastFact {
// 		execState := exec.factStmt(curFact)
// 		if execState.IsNotTrue() {
// 			return execState
// 		}
// 	}

// 	return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)
// }

func (exec *Executor) execClaimStmtProve(stmt *ast.ClaimProveStmt) ast.StmtRet {
	state := exec.claimStmtProve(stmt)
	if state.IsNotTrue() {
		return state
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.ToCheckFact)
	if ret.IsErr() {
		return ast.NewErrStmtEmptyRet(stmt).AddInfer(ret)
	}
	// exec.knowStmt(ast.NewKnowStmt([]ast.CanBeKnownStmt{stmt.ToCheckFact}))

	if ret.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt).AddInfer(ret)
	} else {
		return ast.NewTrueStmtEmptyRet(stmt).AddInfer(ret)
	}

}

func (exec *Executor) execClaimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) ast.StmtRet {
	state := exec.claimStmtProveByContradiction(stmt)
	if state.IsNotTrue() {
		return state
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.ToCheckFact)
	if ret.IsErr() {
		return ast.NewErrStmtEmptyRet(stmt).AddInfer(ret)
	}

	return ast.NewTrueStmtEmptyRet(stmt).AddInfer(ret)
}

// func (exec *Executor) execImpossibleStmt(stmt *ast.ImpossibleStmt) ast.StmtRet{
// 	state := exec.impossibleStmt(stmt)
// 	if state.IsNotTrue() {
// 		return state
// 	}

// 	// 检查 stmt fact 中的所有元素已经定义过了
// 	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.Fact)
// 	if ret.IsErr() {
// 		return ast.StmtErrRet(ret.String())
// 	}

// 	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(state.InnerStmtRetSlice)
// }

// func (exec *Executor) impossibleStmt(stmt *ast.ImpossibleStmt) ast.StmtRet{
// 	exec.NewEnv()
// 	defer func() {
// 		exec.deleteEnv()
// 	}()

// 	// 需要检查 stmt.Fact 里的东西都是在外部声明好了的
// 	ret := exec.Env.LookUpNamesInFact(stmt.Fact, map[string]struct{}{})
// 	if ret.IsErr() {
// 		ret.AddError("in impossible statement")
// 		return ast.StmtErrRet(ret.String())
// 	}

// 	// check that the fact is impossible (i.e., its negation is true)
// 	execState = exec.factStmt(stmt.Fact)
// 	if execState.IsTrue() {
// 		// If the fact is true, then it's not impossible - this is an error
// 		return ast.StmtErrRet(fmt.Sprintf("impossible statement error: the fact is actually true, not impossible:\n%s", stmt.Fact))
// 	}
// 	if execState.IsUnknown() {
// 		return ast.StmtErrRet(fmt.Sprintf("impossible statement error: cannot determine if the fact is impossible:\n%s", stmt.Fact))
// 	}
// 	// If execState.IsNotTrue(), then the fact is indeed impossible, which is what we want
// 	innerStmtRets = append(innerStmtRets, execState)
// 	return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)
// }

func (exec *Executor) claimStmtProve(stmt *ast.ClaimProveStmt) ast.StmtRet {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// 需要检查stmt.ToCheckFact里的东西都是在外部声明好了的
	ret := exec.Env.LookUpNamesInFact(stmt.ToCheckFact, map[string]struct{}{})
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}

	switch stmt.ToCheckFact.(type) {
	case *ast.UniFactStmt:
		isSuccess := exec.claimStmtProveUniFact(stmt)
		if isSuccess.IsNotTrue() {
			return isSuccess
		}
		return isSuccess
	default:
		innerStmtRets := []ast.StmtRet{}
		execState := exec.execStmtsAtCurEnv(stmt.Proofs)
		if execState.IsNotTrue() {
			return execState
		}
		innerStmtRets = append(innerStmtRets, execState)
		// check claim
		execState = exec.factStmt(stmt.ToCheckFact)
		if execState.IsNotTrue() {
			return execState
		}
		innerStmtRets = append(innerStmtRets, execState)
		return ast.NewTrueStmtEmptyRet(stmt).AddInnerStmtRets(innerStmtRets)
	}

}

// prove uniFact in claim at current env
func (exec *Executor) claimStmtProveUniFact(stmt *ast.ClaimProveStmt) ast.StmtRet {
	asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt)
	if !ok {
		return ast.StmtErrRet(stmt, fmt.Sprintf("claim stmt prove uni fact only support uni fact"))
	}

	innerStmtRets := []ast.StmtRet{}

	// declare parameters in asUnivFact in the env
	objDefStmt := ast.NewDefLetStmt(asUnivFact.Params, asUnivFact.ParamSets, []ast.FactStmt{}, stmt.Line)

	execState := exec.defLetStmt(objDefStmt)
	if execState.IsNotTrue() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("Claim statement error: Failed to declare parameters in universal fact:\n%s\n", objDefStmt))
	}
	innerStmtRets = append(innerStmtRets, execState)

	// know dom facts
	for _, domFact := range asUnivFact.DomFacts {
		ret := exec.Env.NewFactWithCheckingNameDefined(domFact)
		if ret.IsErr() {
			return ast.NewErrStmtEmptyRet(stmt).AddInfer(ret)
		}
	}

	// exec proof block
	execState = exec.execStmtsAtCurEnv(stmt.Proofs)
	if execState.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(execState.String())
	}
	innerStmtRets = append(innerStmtRets, execState)

	// TODO: 让claim能forall if
	// if asUnivFact.IffFacts == nil || len(asUnivFact.IffFacts) == 0 {
	// execState, failedFact, err := verifier.ExecFactsAtCurEnv_retFailedFact(asUnivFact.ThenFacts, exec.env, verifier.Round0NoMsg)
	execState, failedFact, err := exec.verifyFactsAtCurEnv(asUnivFact.ThenFacts.ToFactStmtSlice(), Round0NoMsg())
	if err != nil {
		return ast.StmtErrRet(stmt, fmt.Sprintf("claim statement error: failed to verify fact:\n%s\n%s", failedFact, err))
	} else if execState.IsUnknown() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("claim statement error: failed to verify fact:\n%s", failedFact))
	}

	return ast.NewTrueStmtEmptyRet(stmt).AddInnerStmtRets(innerStmtRets)

}

func (exec *Executor) claimIffStmt(stmt *ast.ClaimIffStmt) ast.StmtRet {
	innerStmtRets := []ast.StmtRet{}

	thenToIff := stmt.UniFactWithIffStmt.NewUniFactWithThenToIff()
	iffToThen := stmt.UniFactWithIffStmt.NewUniFactWithIffToThen()
	claimThenToIff := ast.NewClaimProveStmt(thenToIff, stmt.ProofThenToIff, stmt.Line)
	claimIffToThen := ast.NewClaimProveStmt(iffToThen, stmt.ProofIffToThen, stmt.Line)
	execState := exec.claimStmtProve(claimThenToIff)
	if execState.IsNotTrue() {
		return execState
	}
	innerStmtRets = append(innerStmtRets, execState)
	execState = exec.claimStmtProve(claimIffToThen)
	if execState.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt).AddInnerStmtRets(innerStmtRets)
	}
	innerStmtRets = append(innerStmtRets, execState)

	ret := exec.Env.NewFactWithCheckingNameDefined(thenToIff)
	if ret.IsErr() {
		return ast.NewErrStmtEmptyRet(stmt).AddInfer(ret)
	}
	ret = exec.Env.NewFactWithCheckingNameDefined(iffToThen)
	if ret.IsErr() {
		return ast.NewErrStmtEmptyRet(stmt).AddInfer(ret)
	}

	return ast.NewTrueStmtEmptyRet(stmt).AddInnerStmtRets(innerStmtRets)
}
